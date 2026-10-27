module

public import CFSG.LieType.SeitzGeneration.ExcSeitzWide

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Seitz

section Transport


theorem fieldAutData_of_untwistedChevalleyModel {L : Type} [Group L] {τ : Tag} {q p : ℕ}
    (hM : UntwistedChevalleyModel L τ q) (hp : p.Prime)
    (h : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q → FieldAutData (adjointGroup τ K) p) :
    FieldAutData L p := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hM
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  exact (h K hK).of_mulEquiv
    (e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)) hp

end Transport

section Families


theorem fieldAutData_five_chevalley_untwisted {L : Type} [Group L] [Finite L]
    {t : CFSG.Open.StatedLieTag} {ℓ f : ℕ}
    (ht : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hM : CFSG.Blueprint.ChevalleyExceptionalModel L t ℓ f) (hℓ : ℓ ≠ 5) :
    CFSG.RankThree.PartOne.CTP.FieldAutData L 5 := by
  obtain ⟨⟨hℓp, hf, hadm⟩, hU⟩ := hM
  have hp5 : (5 : ℕ).Prime := by norm_num
  have h5K : ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f → 5 ≠ ringChar K :=
    fun K _ _ hK h => hℓ (h.trans (G2Noninner.ringChar_eq_of_card_pow hℓp hf hK)).symm
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, h3⟩ := hadm
    refine fieldAutData_of_untwistedChevalleyModel hU hp5 fun K _ _ hK => ?_
    obtain rfl | hℓ2 := eq_or_ne ℓ 2
    · have hf2 : 2 ≤ f := by
        by_contra hlt
        have h1 : f = 1 := by omega
        rw [h1, pow_one] at h3
        omega
      exact SEITZ2.fieldAutData_G2 (SEITZ2.subfieldPairG2_of_f2 SEITZ2.subfieldPairG2F2) hp5
        le_rfl hf2 hK
    obtain rfl | hℓ3 := eq_or_ne ℓ 3
    · exact G2Noninner.fieldAutData_G2_three G2Noninner.subfieldPairG2Odd hf hK hp5 le_rfl
    · exact G2Noninner.fieldAutData_G2_odd_ne_three G2Noninner.subfieldPairG2Odd hℓp hℓ2 hℓ3 hf
        hK hp5 le_rfl
  · exact fieldAutData_of_untwistedChevalleyModel hU hp5 fun K _ _ hK =>
      ExcOuterLeOne.fieldAutData_F4_of_odd hp5 (by norm_num) (h5K K hK)
  · exact fieldAutData_of_untwistedChevalleyModel hU hp5 fun K _ _ hK =>
      fieldAutData_E6_of_subfieldMaximalAll ExcOuterLeOne.subfieldMaximalAll_E6 hp5 le_rfl
        (h5K K hK)
  · exact fieldAutData_of_untwistedChevalleyModel hU hp5 fun K _ _ hK =>
      ExcOuterLeOne.fieldAutData_E7_of_odd hp5 (by norm_num) (h5K K hK)
  · exact fieldAutData_of_untwistedChevalleyModel hU hp5 fun K _ _ hK =>
      ExcOuterLeOne.fieldAutData_E8_of_odd hp5 (by norm_num) (h5K K hK)

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
