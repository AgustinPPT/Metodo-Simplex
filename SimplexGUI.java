import javax.swing.*;
import javax.swing.border.*;
import javax.swing.table.*;
import java.awt.*;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.*;
import java.util.List;

public class SimplexGUI extends JFrame {

    // =====================================================================
    //  Fracciones exactas
    // =====================================================================
    static final class Frac implements Comparable<Frac> {
        final BigInteger n, d;
        static final Frac ZERO = new Frac(BigInteger.ZERO, BigInteger.ONE);
        static final Frac ONE = new Frac(BigInteger.ONE, BigInteger.ONE);

        Frac(BigInteger num, BigInteger den) {
            if (den.signum() == 0) throw new ArithmeticException("División entre cero");
            if (den.signum() < 0) { num = num.negate(); den = den.negate(); }
            BigInteger g = num.gcd(den);
            if (g.signum() != 0 && !g.equals(BigInteger.ONE)) { num = num.divide(g); den = den.divide(g); }
            n = num; d = den;
        }

        static Frac of(long v) { return new Frac(BigInteger.valueOf(v), BigInteger.ONE); }

        /** Acepta enteros, decimales (0.5 o 0,5) y fracciones (1/3). Vacío = 0. */
        static Frac parse(String s) {
            if (s == null) return ZERO;
            s = s.trim().replace(',', '.');
            if (s.isEmpty()) return ZERO;
            if (s.contains("/")) {
                String[] p = s.split("/");
                if (p.length != 2) throw new NumberFormatException(s);
                return parse(p[0]).div(parse(p[1]));
            }
            BigDecimal bd = new BigDecimal(s);
            if (bd.scale() >= 0)
                return new Frac(bd.unscaledValue(), BigInteger.TEN.pow(bd.scale()));
            return new Frac(bd.unscaledValue().multiply(BigInteger.TEN.pow(-bd.scale())), BigInteger.ONE);
        }

        Frac add(Frac o) { return new Frac(n.multiply(o.d).add(o.n.multiply(d)), d.multiply(o.d)); }
        Frac sub(Frac o) { return new Frac(n.multiply(o.d).subtract(o.n.multiply(d)), d.multiply(o.d)); }
        Frac mul(Frac o) { return new Frac(n.multiply(o.n), d.multiply(o.d)); }
        Frac div(Frac o) { return new Frac(n.multiply(o.d), d.multiply(o.n)); }
        Frac neg() { return new Frac(n.negate(), d); }
        int signum() { return n.signum(); }
        boolean isZero() { return n.signum() == 0; }

        public int compareTo(Frac o) { return n.multiply(o.d).compareTo(o.n.multiply(d)); }

        @Override public String toString() {
            if (d.equals(BigInteger.ONE)) return n.toString();
            if (d.compareTo(BigInteger.valueOf(1000)) <= 0) return n + "/" + d;
            return new BigDecimal(n).divide(new BigDecimal(d), 4, RoundingMode.HALF_UP).toPlainString();
        }
    }

    // =====================================================================
    //  Algoritmo simplex de dos fases
    // =====================================================================
    static final class Paso {
        String fase, titulo, mensaje;
        String[] columnas, base;
        Frac[][] T;
        Frac[] z;
        int filaPiv = -1, colPiv = -1;
    }

    static final class Resultado {
        String estado;               // "optimo", "no_factible", "no_acotado"
        Frac[] x;
        LinkedHashMap<String, Frac> holguras = new LinkedHashMap<>();
        Frac z;
        boolean multiples;
        List<Paso> pasos = new ArrayList<>();
    }

    static final class Simplex {
        static Frac[] filaZ(List<Frac[]> T, List<Integer> B, Frac[] costo, int ncols) {
            Frac[] z = new Frac[ncols + 1];
            for (int j = 0; j <= ncols; j++) {
                Frac s = Frac.ZERO;
                for (int i = 0; i < T.size(); i++) s = s.add(costo[B.get(i)].mul(T.get(i)[j]));
                z[j] = (j < ncols) ? s.sub(costo[j]) : s;
            }
            return z;
        }

        static void pivotear(List<Frac[]> T, int fp, int cp) {
            Frac[] fila = T.get(fp);
            Frac piv = fila[cp];
            for (int j = 0; j < fila.length; j++) fila[j] = fila[j].div(piv);
            for (int i = 0; i < T.size(); i++) {
                if (i == fp) continue;
                Frac[] r = T.get(i);
                Frac f = r[cp];
                if (f.isZero()) continue;
                for (int j = 0; j < r.length; j++) r[j] = r[j].sub(f.mul(fila[j]));
            }
        }

        static Paso foto(String fase, int it, List<Frac[]> T, List<Integer> B, List<String> nombres, Frac[] z) {
            Paso p = new Paso();
            p.fase = fase;
            p.titulo = fase + "  —  Tabla " + it;
            p.columnas = nombres.toArray(new String[0]);
            p.base = new String[B.size()];
            for (int i = 0; i < B.size(); i++) p.base[i] = nombres.get(B.get(i));
            p.T = new Frac[T.size()][];
            for (int i = 0; i < T.size(); i++) p.T[i] = T.get(i).clone();
            p.z = z.clone();
            return p;
        }

        /** Iteraciones simplex (maximizando). Devuelve "optimo" o "no_acotado". */
        static String iterar(List<Frac[]> T, List<Integer> B, Frac[] costo, List<String> nombres,
                             List<Paso> pasos, String fase) {
            int ncols = nombres.size();
            for (int it = 0; it < 1000; it++) {
                Frac[] z = filaZ(T, B, costo, ncols);
                Paso p = foto(fase, it, T, B, nombres, z);
                pasos.add(p);

                // Variable que entra: zj - cj más negativo (empate -> menor índice)
                int entra = -1;
                for (int j = 0; j < ncols; j++)
                    if (z[j].signum() < 0 && (entra < 0 || z[j].compareTo(z[entra]) < 0)) entra = j;
                if (entra < 0) {
                    p.mensaje = "Todos los zj − cj ≥ 0  →  tabla óptima.";
                    return "optimo";
                }

                // Variable que sale: cociente mínimo
                int sale = -1;
                Frac mejor = null;
                for (int i = 0; i < T.size(); i++) {
                    Frac a = T.get(i)[entra];
                    if (a.signum() > 0) {
                        Frac r = T.get(i)[ncols].div(a);
                        int cmp = (mejor == null) ? -1 : r.compareTo(mejor);
                        if (cmp < 0 || (cmp == 0 && B.get(i) < B.get(sale))) { mejor = r; sale = i; }
                    }
                }
                if (sale < 0) {
                    p.colPiv = entra;
                    p.mensaje = "Entra " + nombres.get(entra) + ", pero ningún coeficiente de su columna es "
                              + "positivo  →  solución NO ACOTADA.";
                    return "no_acotado";
                }
                p.filaPiv = sale;
                p.colPiv = entra;
                p.mensaje = "Entra " + nombres.get(entra) + "   ·   Sale " + nombres.get(B.get(sale))
                          + "   ·   Pivote = " + T.get(sale)[entra]
                          + "   ·   Cociente mínimo = " + mejor;
                pivotear(T, sale, entra);
                B.set(sale, entra);
            }
            throw new IllegalStateException("Demasiadas iteraciones");
        }

        static Resultado resolver(Frac[] c, Frac[][] A0, Frac[] b0, String[] tipos0, boolean maximizar) {
            int m = A0.length, n = c.length;
            Resultado res = new Resultado();

            Frac[] cMax = new Frac[n];
            for (int j = 0; j < n; j++) cMax[j] = maximizar ? c[j] : c[j].neg();

            Frac[][] A = new Frac[m][];
            Frac[] b = b0.clone();
            String[] tipos = tipos0.clone();
            for (int i = 0; i < m; i++) {
                A[i] = A0[i].clone();
                if (b[i].signum() < 0) {                       // lado derecho no negativo
                    for (int j = 0; j < n; j++) A[i][j] = A[i][j].neg();
                    b[i] = b[i].neg();
                    tipos[i] = tipos[i].equals("<=") ? ">=" : tipos[i].equals(">=") ? "<=" : "=";
                }
            }

            // Columnas: x | holguras/excesos | artificiales
            List<String> nombres = new ArrayList<>();
            for (int j = 0; j < n; j++) nombres.add("x" + (j + 1));
            List<List<Frac>> filas = new ArrayList<>();
            for (int i = 0; i < m; i++) filas.add(new ArrayList<>(Arrays.asList(A[i])));
            int[] base = new int[m];
            Arrays.fill(base, -1);

            int nh = 0;
            for (int i = 0; i < m; i++) {
                if (tipos[i].equals("<=") || tipos[i].equals(">=")) {
                    nombres.add("s" + (++nh));
                    for (List<Frac> f : filas) f.add(Frac.ZERO);
                    filas.get(i).set(nombres.size() - 1, tipos[i].equals("<=") ? Frac.ONE : Frac.ONE.neg());
                    if (tipos[i].equals("<=")) base[i] = nombres.size() - 1;
                }
            }
            int inicioArt = nombres.size(), na = 0;
            for (int i = 0; i < m; i++) {
                if (tipos[i].equals(">=") || tipos[i].equals("=")) {
                    nombres.add("a" + (++na));
                    for (List<Frac> f : filas) f.add(Frac.ZERO);
                    filas.get(i).set(nombres.size() - 1, Frac.ONE);
                    base[i] = nombres.size() - 1;
                }
            }

            List<Frac[]> T = new ArrayList<>();
            List<Integer> B = new ArrayList<>();
            for (int i = 0; i < m; i++) {
                List<Frac> f = new ArrayList<>(filas.get(i));
                f.add(b[i]);
                T.add(f.toArray(new Frac[0]));
                B.add(base[i]);
            }

            // ---------------- FASE 1 ----------------
            if (na > 0) {
                int ncols = nombres.size();
                Frac[] costo1 = new Frac[ncols];
                for (int j = 0; j < ncols; j++) costo1[j] = j < inicioArt ? Frac.ZERO : Frac.ONE.neg();
                iterar(T, B, costo1, nombres, res.pasos, "Fase 1");
                Frac w = filaZ(T, B, costo1, ncols)[ncols];
                if (w.signum() < 0) {
                    res.estado = "no_factible";
                    return res;
                }
                // Sacar artificiales que quedaron en la base con valor 0
                for (int i = 0; i < T.size(); ) {
                    if (B.get(i) >= inicioArt) {
                        int col = -1;
                        for (int j = 0; j < inicioArt; j++) if (!T.get(i)[j].isZero()) { col = j; break; }
                        if (col >= 0) { pivotear(T, i, col); B.set(i, col); }
                        else { T.remove(i); B.remove(i); continue; }   // restricción redundante
                    }
                    i++;
                }
                // Quitar columnas artificiales
                for (int i = 0; i < T.size(); i++) {
                    Frac[] r = T.get(i);
                    Frac[] nr = Arrays.copyOf(r, inicioArt + 1);
                    nr[inicioArt] = r[r.length - 1];
                    T.set(i, nr);
                }
                nombres = new ArrayList<>(nombres.subList(0, inicioArt));
            }

            // ---------------- FASE 2 ----------------
            int ncols = nombres.size();
            Frac[] costo2 = new Frac[ncols];
            for (int j = 0; j < ncols; j++) costo2[j] = j < n ? cMax[j] : Frac.ZERO;
            String estado = iterar(T, B, costo2, nombres, res.pasos, na > 0 ? "Fase 2" : "Simplex");
            if (estado.equals("no_acotado")) { res.estado = "no_acotado"; return res; }

            Frac[] z = filaZ(T, B, costo2, ncols);
            Frac[] val = new Frac[ncols];
            Arrays.fill(val, Frac.ZERO);
            for (int i = 0; i < B.size(); i++) val[B.get(i)] = T.get(i)[ncols];

            res.estado = "optimo";
            res.x = Arrays.copyOf(val, n);
            for (int j = n; j < ncols; j++) res.holguras.put(nombres.get(j), val[j]);
            res.z = maximizar ? z[ncols] : z[ncols].neg();
            for (int j = 0; j < ncols; j++)
                if (!B.contains(j) && z[j].isZero()) { res.multiples = true; break; }
            return res;
        }
    }

    // =====================================================================
    //  Interfaz gráfica
    // =====================================================================
    private static final Color AZUL = new Color(37, 99, 235);
    private static final Color PIVOTE = new Color(251, 146, 60);
    private static final Color FILA_COL = new Color(254, 243, 199);
    private static final Color FILA_Z = new Color(241, 245, 249);
    private static final Color FILA_OBJ = new Color(219, 234, 254);
    private static final Color ROJO = new Color(220, 38, 38);
    private static final Color VERDE = new Color(22, 163, 74);

    private final JComboBox<String> cbObjetivo = new JComboBox<>(new String[]{"Maximizar", "Minimizar"});
    private final JSpinner spVars = new JSpinner(new SpinnerNumberModel(2, 1, 30, 1));
    private final JSpinner spRes = new JSpinner(new SpinnerNumberModel(3, 1, 30, 1));
    private final JTable tablaEntrada = new JTable();
    private DefaultTableModel modelo;
    private final JPanel panelResultados = new JPanel();
    private final JScrollPane scrollResultados;

    public SimplexGUI() {
        super("Método Simplex — Programación Lineal");
        setDefaultCloseOperation(EXIT_ON_CLOSE);

        // ---- Barra de configuración ----
        JPanel config = new JPanel(new FlowLayout(FlowLayout.LEFT, 10, 8));
        config.add(new JLabel("Objetivo:"));
        config.add(cbObjetivo);
        config.add(new JLabel("   Variables:"));
        config.add(spVars);
        config.add(new JLabel("   Restricciones:"));
        config.add(spRes);
        JButton btCrear = new JButton("Crear tabla");
        config.add(btCrear);
        config.add(new JLabel("     Ejemplos:"));
        JComboBox<String> cbEjemplos = new JComboBox<>(new String[]{
                "— Elegir —", "1. Maximización clásica", "2. Minimización (≥ y =)",
                "3. No factible", "4. No acotado", "5. Óptimos múltiples"});
        config.add(cbEjemplos);

        // ---- Tabla de captura ----
        tablaEntrada.setRowHeight(26);
        tablaEntrada.setFont(tablaEntrada.getFont().deriveFont(14f));
        tablaEntrada.getTableHeader().setFont(tablaEntrada.getFont().deriveFont(Font.BOLD));
        tablaEntrada.setSurrendersFocusOnKeystroke(true);
        tablaEntrada.putClientProperty("terminateEditOnFocusLost", Boolean.TRUE);
        tablaEntrada.setDefaultRenderer(Object.class, new RendererEntrada());
        JScrollPane scEntrada = new JScrollPane(tablaEntrada);
        scEntrada.setBorder(new TitledBorder("Datos del problema  (fila Z = función objetivo; acepta 3, -2, 0.5 o 1/3)"));

        // ---- Botones ----
        JPanel botones = new JPanel(new FlowLayout(FlowLayout.LEFT, 10, 6));
        JButton btResolver = new JButton("▶  Resolver");
        btResolver.setFont(btResolver.getFont().deriveFont(Font.BOLD, 14f));
        btResolver.setBackground(AZUL);
        btResolver.setForeground(Color.WHITE);
        JButton btLimpiar = new JButton("Limpiar resultados");
        botones.add(btResolver);
        botones.add(btLimpiar);
        JLabel leyenda = new JLabel("<html>&nbsp;&nbsp;<span style='background:#FB923C'>&nbsp;pivote&nbsp;</span>"
                + "&nbsp;&nbsp;<span style='background:#FEF3C7'>&nbsp;fila/columna pivote&nbsp;</span>"
                + "&nbsp;&nbsp;<font color='#DC2626'>zj − cj negativo</font></html>");
        botones.add(leyenda);

        JPanel arriba = new JPanel(new BorderLayout());
        arriba.add(config, BorderLayout.NORTH);
        arriba.add(scEntrada, BorderLayout.CENTER);
        arriba.add(botones, BorderLayout.SOUTH);

        // ---- Resultados ----
        panelResultados.setLayout(new BoxLayout(panelResultados, BoxLayout.Y_AXIS));
        panelResultados.setBorder(new EmptyBorder(8, 8, 8, 8));
        JPanel contenedor = new JPanel(new BorderLayout());
        contenedor.add(panelResultados, BorderLayout.NORTH);
        scrollResultados = new JScrollPane(contenedor);
        scrollResultados.getVerticalScrollBar().setUnitIncrement(16);
        scrollResultados.setBorder(new TitledBorder("Solución paso a paso"));

        JSplitPane split = new JSplitPane(JSplitPane.VERTICAL_SPLIT, arriba, scrollResultados);
        split.setDividerLocation(300);
        split.setResizeWeight(0.3);
        add(split);

        // ---- Eventos ----
        btCrear.addActionListener(e -> crearTabla());
        btResolver.addActionListener(e -> resolver());
        btLimpiar.addActionListener(e -> { panelResultados.removeAll(); panelResultados.revalidate(); panelResultados.repaint(); });
        cbEjemplos.addActionListener(e -> {
            int k = cbEjemplos.getSelectedIndex();
            if (k > 0) { cargarEjemplo(k); cbEjemplos.setSelectedIndex(0); }
        });

        crearTabla();
        setSize(1150, 800);
        setLocationRelativeTo(null);
    }

    private void crearTabla() {
        int n = (Integer) spVars.getValue(), m = (Integer) spRes.getValue();
        String[] cols = new String[n + 3];
        cols[0] = "";
        for (int j = 0; j < n; j++) cols[j + 1] = "x" + (j + 1);
        cols[n + 1] = "Signo";
        cols[n + 2] = "Lado derecho";
        modelo = new DefaultTableModel(cols, m + 1) {
            @Override public boolean isCellEditable(int r, int c) {
                return c != 0 && !(r == 0 && c >= n + 1);
            }
        };
        modelo.setValueAt("Z", 0, 0);
        modelo.setValueAt("—", 0, n + 1);
        modelo.setValueAt("—", 0, n + 2);
        for (int i = 1; i <= m; i++) {
            modelo.setValueAt("R" + i, i, 0);
            modelo.setValueAt("<=", i, n + 1);
        }
        tablaEntrada.setModel(modelo);
        tablaEntrada.getColumnModel().getColumn(0).setMaxWidth(50);
        tablaEntrada.getColumnModel().getColumn(n + 1)
                .setCellEditor(new DefaultCellEditor(new JComboBox<>(new String[]{"<=", ">=", "="})));
        tablaEntrada.getColumnModel().getColumn(n + 1).setMaxWidth(90);
    }

    private void cargarEjemplo(int k) {
        Object[][] filas;
        String obj;
        switch (k) {
            case 1: obj = "Maximizar"; filas = new Object[][]{
                    {"3", "5"}, {"1", "0", "<=", "4"}, {"0", "2", "<=", "12"}, {"3", "2", "<=", "18"}}; break;
            case 2: obj = "Minimizar"; filas = new Object[][]{
                    {"2", "3"}, {"0.5", "0.25", "<=", "4"}, {"1", "3", ">=", "20"}, {"1", "1", "=", "10"}}; break;
            case 3: obj = "Maximizar"; filas = new Object[][]{
                    {"1", "1"}, {"1", "1", "<=", "2"}, {"1", "1", ">=", "5"}}; break;
            case 4: obj = "Maximizar"; filas = new Object[][]{
                    {"2", "1"}, {"1", "-1", "<=", "10"}, {"2", "-1", "<=", "40"}}; break;
            default: obj = "Maximizar"; filas = new Object[][]{
                    {"2", "4"}, {"1", "2", "<=", "5"}, {"1", "1", "<=", "4"}}; break;
        }
        cbObjetivo.setSelectedItem(obj);
        spVars.setValue(2);
        spRes.setValue(filas.length - 1);
        crearTabla();
        modelo.setValueAt(filas[0][0], 0, 1);
        modelo.setValueAt(filas[0][1], 0, 2);
        for (int i = 1; i < filas.length; i++)
            for (int j = 0; j < 4; j++) modelo.setValueAt(filas[i][j], i, j + 1);
        resolver();
    }

    private void resolver() {
        if (tablaEntrada.isEditing()) tablaEntrada.getCellEditor().stopCellEditing();
        int n = modelo.getColumnCount() - 3, m = modelo.getRowCount() - 1;
        Frac[] c = new Frac[n];
        Frac[][] A = new Frac[m][n];
        Frac[] b = new Frac[m];
        String[] tipos = new String[m];
        int r = 0, col = 0;
        try {
            for (col = 1; col <= n; col++) c[col - 1] = Frac.parse(str(modelo.getValueAt(0, col)));
            for (r = 1; r <= m; r++) {
                for (col = 1; col <= n; col++) A[r - 1][col - 1] = Frac.parse(str(modelo.getValueAt(r, col)));
                col = n + 2;
                b[r - 1] = Frac.parse(str(modelo.getValueAt(r, n + 2)));
                tipos[r - 1] = str(modelo.getValueAt(r, n + 1));
            }
        } catch (RuntimeException ex) {
            JOptionPane.showMessageDialog(this,
                    "Valor no válido en la fila " + (r == 0 ? "Z" : "R" + r) + ", columna "
                            + modelo.getColumnName(col) + ".\nUsa números como 3, -2, 0.5 o 1/3.",
                    "Error de captura", JOptionPane.ERROR_MESSAGE);
            return;
        }
        boolean max = cbObjetivo.getSelectedIndex() == 0;
        Resultado res = Simplex.resolver(c, A, b, tipos, max);
        mostrar(res, c, A, b, tipos, max);
    }

    private static String str(Object o) { return o == null ? "" : o.toString(); }

    // ---------------------------------------------------------------------
    //  Dibujo de resultados
    // ---------------------------------------------------------------------
    private void mostrar(Resultado res, Frac[] c, Frac[][] A, Frac[] b, String[] tipos, boolean max) {
        panelResultados.removeAll();

        // Planteamiento
        StringBuilder sb = new StringBuilder("<html><div style='font-size:12px'><b>")
                .append(max ? "Maximizar" : "Minimizar").append("</b> &nbsp;Z = ").append(expr(c))
                .append("<br><b>Sujeto a:</b><br>");
        for (int i = 0; i < A.length; i++)
            sb.append("&nbsp;&nbsp;&nbsp;").append(expr(A[i])).append(" ")
              .append(tipos[i].replace("<=", "≤").replace(">=", "≥")).append(" ").append(b[i]).append("<br>");
        sb.append("&nbsp;&nbsp;&nbsp;");
        for (int j = 0; j < c.length; j++) sb.append(j > 0 ? ", " : "").append("x").append(j + 1);
        sb.append(" ≥ 0</div></html>");
        agregar(new JLabel(sb.toString()));

        String faseActual = "";
        for (Paso p : res.pasos) {
            if (!p.fase.equals(faseActual)) {
                faseActual = p.fase;
                String texto = p.fase.equals("Fase 1") ? "FASE 1 — Minimizar la suma de variables artificiales"
                        : p.fase.equals("Fase 2") ? "FASE 2 — Optimizar la función objetivo original"
                        : "MÉTODO SIMPLEX";
                JLabel h = new JLabel(texto);
                h.setFont(h.getFont().deriveFont(Font.BOLD, 15f));
                h.setForeground(AZUL);
                h.setBorder(new EmptyBorder(14, 0, 4, 0));
                agregar(h);
            }
            agregar(panelPaso(p));
        }
        agregar(panelFinal(res, max));

        panelResultados.revalidate();
        panelResultados.repaint();
        SwingUtilities.invokeLater(() -> scrollResultados.getVerticalScrollBar().setValue(0));
    }

    private static String expr(Frac[] coef) {
        StringBuilder sb = new StringBuilder();
        for (int j = 0; j < coef.length; j++) {
            Frac v = coef[j];
            Frac abs = v.signum() < 0 ? v.neg() : v;
            String num = abs.compareTo(Frac.ONE) == 0 ? "" : abs.d.equals(BigInteger.ONE) ? abs.toString() : "(" + abs + ")";
            if (j == 0) sb.append(v.signum() < 0 ? "−" : "").append(num);
            else sb.append(v.signum() < 0 ? " − " : " + ").append(num);
            sb.append("x").append(j + 1);
        }
        return sb.toString();
    }

    private void agregar(JComponent comp) {
        comp.setAlignmentX(Component.LEFT_ALIGNMENT);
        if (!(comp instanceof JLabel))
            comp.setMaximumSize(new Dimension(Integer.MAX_VALUE, comp.getPreferredSize().height));
        panelResultados.add(comp);
        panelResultados.add(Box.createVerticalStrut(6));
    }

    private JPanel panelPaso(Paso p) {
        int ncols = p.columnas.length;
        String[] enc = new String[ncols + 2];
        enc[0] = "Base";
        System.arraycopy(p.columnas, 0, enc, 1, ncols);
        enc[ncols + 1] = "LD";
        Object[][] datos = new Object[p.T.length + 1][ncols + 2];
        for (int i = 0; i < p.T.length; i++) {
            datos[i][0] = p.base[i];
            for (int j = 0; j <= ncols; j++) datos[i][j + 1] = p.T[i][j].toString();
        }
        datos[p.T.length][0] = "Z";
        for (int j = 0; j <= ncols; j++) datos[p.T.length][j + 1] = p.z[j].toString();

        JTable t = new JTable(datos, enc) {
            @Override public boolean isCellEditable(int r, int c) { return false; }
        };
        t.setRowHeight(24);
        t.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 13));
        t.setRowSelectionAllowed(false);
        t.setFocusable(false);
        t.getTableHeader().setReorderingAllowed(false);
        t.getTableHeader().setFont(t.getTableHeader().getFont().deriveFont(Font.BOLD));
        t.setDefaultRenderer(Object.class, new RendererPaso(p));

        JPanel panel = new JPanel(new BorderLayout());
        panel.setBorder(new CompoundBorder(new TitledBorder(p.titulo), new EmptyBorder(4, 4, 4, 4)));
        JPanel tabla = new JPanel(new BorderLayout());
        tabla.add(t.getTableHeader(), BorderLayout.NORTH);
        tabla.add(t, BorderLayout.CENTER);
        tabla.setBorder(new LineBorder(Color.LIGHT_GRAY));
        panel.add(tabla, BorderLayout.CENTER);
        if (p.mensaje != null) {
            JLabel msg = new JLabel(p.mensaje);
            msg.setBorder(new EmptyBorder(6, 2, 0, 0));
            msg.setFont(msg.getFont().deriveFont(Font.BOLD));
            if (p.mensaje.contains("NO ACOTADA")) msg.setForeground(ROJO);
            else if (p.mensaje.contains("óptima")) msg.setForeground(VERDE);
            panel.add(msg, BorderLayout.SOUTH);
        }
        return panel;
    }

    private JPanel panelFinal(Resultado res, boolean max) {
        StringBuilder sb = new StringBuilder("<html><div style='font-size:13px'>");
        Color color;
        if (res.estado.equals("optimo")) {
            color = VERDE;
            sb.append("<b style='font-size:15px'>✔ SOLUCIÓN ÓPTIMA</b><br><br>");
            for (int j = 0; j < res.x.length; j++)
                sb.append("x").append(j + 1).append(" = <b>").append(res.x[j]).append("</b> &nbsp;&nbsp; ");
            sb.append("<br><br><b style='font-size:15px'>Z ").append(max ? "máx" : "mín").append(" = ")
              .append(res.z).append("</b>");
            if (!res.holguras.isEmpty()) {
                sb.append("<br><br><font color='#475569'>Holguras / excesos: ");
                res.holguras.forEach((k, v) -> sb.append(k).append(" = ").append(v).append(" &nbsp; "));
                sb.append("</font>");
            }
            if (res.multiples)
                sb.append("<br><br><font color='#B45309'>Nota: existen <b>soluciones óptimas múltiples</b> "
                        + "(una variable no básica tiene zj − cj = 0).</font>");
        } else if (res.estado.equals("no_factible")) {
            color = ROJO;
            sb.append("<b style='font-size:15px'>✖ EL PROBLEMA NO TIENE SOLUCIÓN FACTIBLE</b><br><br>")
              .append("El óptimo de la Fase 1 es distinto de 0: las restricciones no pueden cumplirse a la vez.");
        } else {
            color = ROJO;
            sb.append("<b style='font-size:15px'>✖ SOLUCIÓN NO ACOTADA</b><br><br>")
              .append("La función objetivo puede crecer indefinidamente sin violar las restricciones.");
        }
        sb.append("</div></html>");
        JLabel l = new JLabel(sb.toString());
        l.setForeground(Color.DARK_GRAY);
        JPanel p = new JPanel(new BorderLayout());
        p.setBackground(Color.WHITE);
        p.setBorder(new CompoundBorder(new MatteBorder(0, 6, 0, 0, color),
                new CompoundBorder(new LineBorder(color), new EmptyBorder(12, 14, 12, 14))));
        p.add(l);
        return p;
    }

    // ---------------------------------------------------------------------
    //  Renderizadores de celdas
    // ---------------------------------------------------------------------
    private static final class RendererEntrada extends DefaultTableCellRenderer {
        @Override public Component getTableCellRendererComponent(JTable t, Object v, boolean sel, boolean foc, int r, int c) {
            super.getTableCellRendererComponent(t, v, sel, foc, r, c);
            setHorizontalAlignment(CENTER);
            setBackground(sel ? t.getSelectionBackground() : r == 0 ? FILA_OBJ : c == 0 ? FILA_Z : Color.WHITE);
            setForeground(sel ? t.getSelectionForeground() : Color.BLACK);
            setFont(getFont().deriveFont(c == 0 || r == 0 ? Font.BOLD : Font.PLAIN));
            return this;
        }
    }

    private static final class RendererPaso extends DefaultTableCellRenderer {
        private final Paso p;
        RendererPaso(Paso p) { this.p = p; }

        @Override public Component getTableCellRendererComponent(JTable t, Object v, boolean sel, boolean foc, int r, int c) {
            super.getTableCellRendererComponent(t, v, false, false, r, c);
            setHorizontalAlignment(CENTER);
            int j = c - 1;
            boolean filaZ = r == p.T.length;
            Color bg = Color.WHITE, fg = Color.BLACK;
            int estilo = Font.PLAIN;

            if (c == 0) { bg = FILA_Z; estilo = Font.BOLD; }
            if (filaZ) {
                bg = FILA_Z; estilo = Font.BOLD;
                if (j >= 0 && j < p.z.length - 1 && p.z[j].signum() < 0) fg = ROJO;
            }
            if (!filaZ && c > 0 && (r == p.filaPiv || j == p.colPiv)) bg = FILA_COL;
            if (r == p.filaPiv && j == p.colPiv) { bg = PIVOTE; estilo = Font.BOLD; }
            if (filaZ && j == p.colPiv && p.colPiv >= 0) { bg = FILA_COL; }

            setBackground(bg);
            setForeground(fg);
            setFont(t.getFont().deriveFont(estilo));
            return this;
        }
    }

    // =====================================================================
    //  main
    // =====================================================================
    public static void main(String[] args) {
        if (args.length > 0 && args[0].equals("--test")) { pruebas(); return; }
        try {
            for (UIManager.LookAndFeelInfo info : UIManager.getInstalledLookAndFeels())
                if ("Nimbus".equals(info.getName())) { UIManager.setLookAndFeel(info.getClassName()); break; }
        } catch (Exception ignored) { }
        SwingUtilities.invokeLater(() -> new SimplexGUI().setVisible(true));
    }

    /** Pruebas en consola, sin interfaz gráfica. */
    private static void pruebas() {
        probar("Max clásica (esperado x=(2,6), Z=36)", new String[]{"3", "5"},
                new String[][]{{"1", "0"}, {"0", "2"}, {"3", "2"}}, new String[]{"4", "12", "18"},
                new String[]{"<=", "<=", "<="}, true);
        probar("Min dos fases (esperado x=(5,5), Z=25)", new String[]{"2", "3"},
                new String[][]{{"0.5", "0.25"}, {"1", "3"}, {"1", "1"}}, new String[]{"4", "20", "10"},
                new String[]{"<=", ">=", "="}, false);
        probar("No factible", new String[]{"1", "1"}, new String[][]{{"1", "1"}, {"1", "1"}},
                new String[]{"2", "5"}, new String[]{"<=", ">="}, true);
        probar("No acotado", new String[]{"2", "1"}, new String[][]{{"1", "-1"}, {"2", "-1"}},
                new String[]{"10", "40"}, new String[]{"<=", "<="}, true);
        probar("Óptimos múltiples (Z=10)", new String[]{"2", "4"}, new String[][]{{"1", "2"}, {"1", "1"}},
                new String[]{"5", "4"}, new String[]{"<=", "<="}, true);
        probar("Min con lado derecho negativo (esperado Z=4)", new String[]{"1", "1"},
                new String[][]{{"-1", "-1"}, {"1", "0"}}, new String[]{"-4", "3"}, new String[]{"<=", "<="}, false);
    }

    private static void probar(String nombre, String[] c, String[][] A, String[] b, String[] t, boolean max) {
        Frac[] fc = Arrays.stream(c).map(Frac::parse).toArray(Frac[]::new);
        Frac[][] fA = Arrays.stream(A).map(f -> Arrays.stream(f).map(Frac::parse).toArray(Frac[]::new)).toArray(Frac[][]::new);
        Frac[] fb = Arrays.stream(b).map(Frac::parse).toArray(Frac[]::new);
        Resultado r = Simplex.resolver(fc, fA, fb, t, max);
        System.out.print(nombre + " -> " + r.estado);
        if (r.estado.equals("optimo"))
            System.out.print("  x=" + Arrays.toString(r.x) + "  Z=" + r.z + (r.multiples ? "  (múltiples)" : ""));
        System.out.println("   [" + r.pasos.size() + " tablas]");
    }
}
