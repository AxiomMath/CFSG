module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XCaseIII
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XCaseI
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XCaseIIa
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XCaseIIb

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

variable {V : Type*} [Group V] {X : Type} [Group X] {ρ : X →* MulAut V} {Q : Subgroup X}
  {V₁ V₂ : Subgroup V} {z : X} {Q₁ : Subgroup (MulAut ↥V₁)} {t₁ : ↥V₁}

theorem XHyp.concl [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (hKD : KDM22)
    (hKg : KCore.KGroupNonab CFSG.Blueprint.Catalog X) : XConcl ρ Q V₁ V₂ z := by
  by_cases h0 : zpowers z ⊔ Q = ⊤
  · exact h.concl_of_eq_top h0
  by_cases hE : layer X = ⊥
  · exact h.concl_of_layer_eq_bot h0 hE
  by_cases hI : ∃ K : Subgroup X, IsComponent K ∧ K.map (MulAut.conj z).toMonoidHom ≠ K
  · obtain ⟨K, hK, hKz⟩ := hI
    exact h.concl_of_map_conj_ne hK hKz
  by_cases hII : ∃ K : Subgroup X, IsComponent K ∧ K ≤ centralizer ({z} : Set X)
  · obtain ⟨K, hK, hKz⟩ := hII
    exact h.concl_of_le_centralizer h0 hK hKz
  push_neg at hI hII
  exact (h.false_of_forall_isComponent h0 hKD hKg hE hI hII).elim

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
