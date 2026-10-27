module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2PglFinal

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem evenSecondBound : EvenSecondBound := by
  intro f hfe F _ _ σ hF hσ y hyσ hy3 _
  have hf : 1 ≤ f := by
    rcases hfe with ⟨k, hk⟩
    have : f ≠ 0 := by
      rintro rfl
      have h1 : Nat.card F = 1 := by simpa using hF
      have : Nontrivial F := inferInstance
      have := Nat.card_pos (α := F)
      haveI : Fintype F := Fintype.ofFinite F
      have := Fintype.one_lt_card (α := F)
      rw [← Nat.card_eq_fintype_card] at this
      omega
    omega
  exact Tri2Pgl.card_fixedSubgroup_second_class_even
    hf hfe σ hF hσ hyσ hy3 (card_fixedSubgroup_sigma0 hf hF hσ ▸ dvd_rfl)

theorem outerFixedOrder_trialityD4_three_even :
    ∀ (K : Type) [Group K] [Finite K] (n f : ℕ), StatedLieAdmissible .trialityD4 n 2 f →
      CFSG.Blueprint.LieModel K .trialityD4 n 2 f →
      ∀ α : MulAut K, α ^ 3 = 1 → α ∉ inner K →
        Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .G2 0 (2 ^ f) :=
  outerFixedOrder_trialityD4_three_even_of_evenSecond evenSecondBound

end CFSG.HardMathSupport.Lang.E6Descent
