module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A512
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A512c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A511Pf
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A511Qi
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A513c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A59S

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem contra14_5_3Solv_of_F4 (h4 : Lemma14_7_4_two_three_F4) : Contra14_5_3Solv_F4 := by
  intro G _ _ T L V V₂ Y C hQ hsolv
  have hJ := C.thompsonJ_le_centralizer_F4 h4 hQ hsolv
  have hX := C.xL_eq_commutator_F4 h4 hQ hsolv
  have hO3 := lemma14_5_11_of_core_F4 lemma14_5_11Core_holds_F4 G T L V V₂ Y C
    (C.quot_xT_F4 h4).1 (C.inf_eq_F4 h4) hQ hsolv hJ hX
  obtain ⟨hne, hcase⟩ := C.lemma14_5_12_F4 h4 hQ hsolv hO3 lemma14_5_12CaseOne_holds_F4
  exact lemma14_5_13Fin_holds_F4 G T L V V₂ Y C (C.quot_xT_F4 h4).1 (C.inf_eq_F4 h4) hQ hsolv hJ hX
    hO3 hne hcase

end CFSG.Quasithin.H13.L32A.T53
