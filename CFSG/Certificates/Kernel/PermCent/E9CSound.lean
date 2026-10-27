module

public import Certificates.Data.Kernel.PermCent.E9C
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import Certificates.Data.L33E9

public section

namespace CFSG.Certificates.Kernel.PkCV.E9

open CFSG.Quasithin.E217L33

theorem nine_ev (a b : CV 26) : nine (ev a) (ev b) = (nineC a b).map ev := by
  simp only [nine, nineC, List.map_cons, List.map_nil, ev_mul', ev_pow', one_eq_ev]

theorem stabList_ev (L : List (CV 26)) (t f : CV 26) :
    stabList (L.map ev) (ev t) (ev f) = (stabC L t f).map ev := by
  unfold stabList stabC
  rw [List.filter_map]
  simp only [Function.comp_def, ev_mul', ev_inv', ev_pow', decide_ev_eq, comm_fast, conj_fast]

theorem e9Check_C (L : List (CV 26)) (t a b : CV 26) :
    e9Check (L.map ev) (ev t) (ev a) (ev b) = e9C L t a b := by
  unfold e9Check e9C
  simp only [nine_ev, stabList_ev, List.length_map, List.all_map, Function.comp_def,
    decide_mem_map_ev, nodup_map_ev, ne_eq, decide_not, ev_mul', ev_inv', one_eq_ev, decide_ev_eq,
    sq_fast, comm_fast, conj_fast]

end CFSG.Certificates.Kernel.PkCV.E9

end
