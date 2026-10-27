module

public import Certificates.Data.Kernel.PermCent.Sp6BTwin
public import CFSG.Certificates.Kernel.PermCent.SmallBSound

public section

namespace CFSG.Certificates.Kernel.PkCV.Sp6B

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier CFSG.GH74.KGroups
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data
  CFSG.ClassicalInvolution.Q3.TL4.E4C

theorem map_tab (l : List (Equiv.Perm (Fin 36))) : l.map tab = l := by
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun σ _ => tab_eq σ

theorem enum_ev (Q : RawSchreierDatum 36) : enumeration Q = (elemsC Q).map ev :=
  (elemsT_eq Q).symm.trans (elemsT_eq_elemsC Q)

theorem L0_ev : L0 () = L0C.map ev := by
  rw [L0.eq_1, q8Elems.eq_1, tab_eq, eq_ev_cOf sp6Rep2, eq_ev_cOf (rho ()), eq_ev_cOf (jay ()),
    L0C.eq_1]
  simp only [List.map_cons, List.map_nil, ev_mul', one_eq_ev]

theorem ws_ev : ws () = wsC.map ev := by
  rw [ws.eq_1, wsC.eq_1, G.eq_1, List.map_map]
  exact List.map_congr_left fun w _ => by rw [tab_eq, Function.comp_apply, ev_evCodesB]

theorem getD_ev (W : List (CV 36)) (k : Nat) : (W.map ev).getD k (ev 1) = ev (W.getD k 1) :=
  List.getD_map ..

theorem L1_ev : L1 () = L1C.map ev := by
  rw [L1.eq_1, twin.eq_1, L0_ev, ws_ev, one_eq_ev, getD_ev, L1C.eq_1, List.map_map, List.map_map]
  exact List.map_congr_left fun y _ => by
    simp only [Function.comp_apply, ev_mul', ev_inv']

theorem commAll_ev (g : CV 36) (l : List (CV 36)) : commAll (ev g) (l.map ev) = commAllC g l := by
  rw [commAll.eq_1, commAllC.eq_1, List.all_map]
  simp only [Function.comp_def, ev_mul', decide_ev_eq]

theorem memberElems_ev (L : List (CV 36)) (w : CV 36) :
    memberElems (L.map ev) (ev w) = (memberElemsC L w).map ev := by
  rw [memberElems.eq_1, memberElemsC.eq_1, List.map_map, List.map_map]
  exact List.map_congr_left fun q _ => by
    simp only [Function.comp_apply, tab_eq, ev_mul', ev_inv']

theorem ordThree_ev (c : CV 36) : ordThree (ev c) = ordThreeC c := by
  rw [ordThree.eq_1, ordThreeC.eq_1]
  simp only [ev_mul', one_eq_ev, decide_ev_eq]

end CFSG.Certificates.Kernel.PkCV.Sp6B

end
