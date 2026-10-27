module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5Basic
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5ExcE6
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5ExcTri

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.TwoL5

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace Exc2

theorem noLitLayer_of_noLitA5 {G : Type} [Group G] (h : C5Exc.NoLitA5 G) : NoLitLayer G := by
  rintro L ⟨hL, hA, hz⟩
  obtain ⟨z, hzc, hz2⟩ := h L hL hA
  have hzz : z * z = 1 := by
    rw [← sq, ← hz2]
    exact pow_orderOf_eq_one z
  have h1 : (z : G) = 1 := hz (z : G) z.2
    (fun y hy => by
      have := mem_center_iff.mp hzc ⟨y, hy⟩
      exact congrArg Subtype.val this.symm)
    (congrArg Subtype.val hzz)
  have hz1 : z = 1 := Subtype.ext h1
  rw [hz1, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem noLitLayer_fixedSubgroup {t : StatedLieTag} (h : C5Exc.OddLieA5For t) {S : Type}
    [Group S] {n f : ℕ} (hm : Blueprint.LieModel S t n 5 f) {σ : MulAut S}
    (hσ : orderOf σ = 2) : NoLitLayer (fixedSubgroup σ) :=
  noLitLayer_of_noLitA5
    (h S n 5 f Nat.prime_five (by norm_num) (by norm_num) hm.admissible hm σ hσ)

theorem fiveTwoLayer_char5_of_oddLieA5For
    {t : StatedLieTag} (h : C5Exc.OddLieA5For t) : FiveTwoLayerCharFiveClause t := by
  intro S _ _ hs hna ⟨n, f, hm⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  exfalso
  haveI := hs
  have hQ : FixedTwoComponentsQuasisimple S :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna
      ⟨t, n, 5, f, Nat.prime_five, by norm_num, hm.admissible, hm⟩
  have hσ1 : σ ≠ 1 := h₁.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h₁.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hT : TwoLayers (fixedSubgroup σ) := twoLayers_of_clause hQ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  exact (noLitLayer_fixedSubgroup h hm hσ2).not_twoLayers hT

end Exc2

theorem fiveTwoLayer_char5_E6 :
    FiveTwoLayerCharFiveClause .E6 :=
  Exc2.fiveTwoLayer_char5_of_oddLieA5For
    (C5Exc.oddLieA5For_E6 CatLeafProof.lieOrderFormulasInput)

theorem fiveTwoLayer_char5_twistedE6 :
    FiveTwoLayerCharFiveClause .twistedE6 :=
  Exc2.fiveTwoLayer_char5_of_oddLieA5For
    (C5Exc.oddLieA5For_twistedE6 CatLeafProof.lieOrderFormulasInput)

theorem fiveTwoLayer_char5_trialityD4 :
    FiveTwoLayerCharFiveClause .trialityD4 :=
  Exc2.fiveTwoLayer_char5_of_oddLieA5For
    (C5Exc.oddLieA5For_trialityD4 CatLeafProof.lieOrderFormulasInput)

end CFSG.ComponentClassification.SolMax.FiveCat.TwoL5
