module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigWTrivial

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G]

theorem exists_not_mem_zpowers_of_isKleinFour {F : Subgroup G} (hF : IsKleinFour F) {a : G}
    (ha : a ∈ F) : ∃ b ∈ F, b ∉ zpowers a := by
  by_contra h
  push Not at h
  have h4 := Subgroup.card_le_of_le (show F ≤ zpowers a from fun x hx => h x hx)
  rw [hF.card_four, Nat.card_zpowers] at h4
  have h2 := orderOf_le_of_pow_eq_one (by norm_num) (Sig.sq_eq_one_of_isKleinFour hF ha)
  omega

theorem solRestricted_of_ncard_ne_two {N K K' : Subgroup G}
    (hr : (kStarComponents N).ncard ≠ 2) : solRestricted G N K K' := by
  intro h2
  exact (hr h2).elim

theorem lemma315bInputFor_simple_of_wTrivialFor_two (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hW : WTrivialFor solRestricted)
    (h2 : ForcedSeparationTwoFor solRestricted) : Lemma315bInputFor simpleAmbient :=
  lemma315bInputFor_simple_of_restricted hq hR1 hW
    (forcedSeparationFor_of_two hq (fun _ _ _ _ _ _ hr => solRestricted_of_ncard_ne_two hr) h2)

end CFSG.ComponentClassification.Sol76.Sig
