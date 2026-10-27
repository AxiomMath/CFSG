module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinF2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadM11
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadL33

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

theorem radData_of_small_model
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hmodel : StatedClassicalModel ↥K .PSL 3 3 1 ∨
      Nonempty (↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) : RadData ↥K := by
  rcases hmodel with h | he
  · exact radData_of_stated_l33 h
  · obtain ⟨e⟩ := he
    exact radData_of_equiv_m11 e

theorem l33M11RadicalCharTwo
    : L33M11RadicalCharTwo := by
  intro G _ _ K R hmodel hRK hR2 hR hrad
  exact charTwo_inf_normalizer_of_radData (radData_of_small_model hmodel) hRK hR2 hR hrad

theorem q8Characteristic
    : Q8Characteristic := by
  intro G _ _ K t hmodel htK hcen R hRK hR2 hle
  exact normalizer_le_normalizer_pCoreOf_of_radData (radData_of_small_model hmodel) htK hcen hR2
    hRK hle

end CFSG.QuasithinUnique.Fin253
