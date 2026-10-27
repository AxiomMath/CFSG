module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5Basic
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5ExcField

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.TwoL5

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint (chevalleyExceptionalTags)

namespace Exc1

theorem noLitLayer_of_noLitA5 {G : Type} [Group G] (h : C5Exc.NoLitA5 G) : NoLitLayer G := by
  rintro L ⟨hL, hA, hz⟩
  obtain ⟨z, hzc, hz2⟩ := h L hL hA
  have hzz : z * z = 1 := by
    rw [← sq, ← hz2]
    exact pow_orderOf_eq_one z
  have h1 : (z : G) = 1 :=
    hz z z.2 (fun y hy => (congrArg Subtype.val (mem_center_iff.mp hzc ⟨y, hy⟩)).symm)
      (congrArg Subtype.val hzz)
  have h2 : z = 1 := Subtype.ext h1
  rw [h2, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem fiveTwoLayer_of_oddLieA5For
    {t : StatedLieTag} (ht : t ∈ chevalleyExceptionalTags) (h : C5Exc.OddLieA5For t) :
    FiveTwoLayerCharFiveClause t := by
  intro S _ _ hs hna ⟨n, f, hm⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  haveI := hs
  have hadm : StatedLieAdmissible t n 5 f := hm.admissible
  have hσ1 : σ ≠ 1 := h₁.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h₁.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hq : ∀ α : MulAut S, α * α = 1 → α ≠ 1 →
      ∀ L : Subgroup (fixedSubgroup α), IsPComponent 2 L → IsQuasisimple L :=
    fixedTwoComponentsQuasisimple_exceptional ht Nat.prime_five (by norm_num)
      (hm.chevalleyExceptionalModel ht)
  have hT : TwoLayers (fixedSubgroup σ) := twoLayers_of_clause hq h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  exact ((noLitLayer_of_noLitA5 (h S n 5 f Nat.prime_five (by norm_num) (by norm_num) hadm hm σ
    hσ2)).not_twoLayers hT).elim

end Exc1

theorem fiveTwoLayer_char5_G2 :
    FiveTwoLayerCharFiveClause .G2 :=
  Exc1.fiveTwoLayer_of_oddLieA5For (by decide)
    (C5Exc.oddLieA5For_G2 CatLeafProof.lieOrderFormulasInput)

theorem fiveTwoLayer_char5_F4 :
    FiveTwoLayerCharFiveClause .F4 :=
  Exc1.fiveTwoLayer_of_oddLieA5For (by decide)
    (C5Exc.oddLieA5For_F4 CatLeafProof.lieOrderFormulasInput)

theorem fiveTwoLayer_char5_E7 :
    FiveTwoLayerCharFiveClause .E7 :=
  Exc1.fiveTwoLayer_of_oddLieA5For (by decide)
    (C5Exc.oddLieA5For_E7 CatLeafProof.lieOrderFormulasInput)

theorem fiveTwoLayer_char5_E8 :
    FiveTwoLayerCharFiveClause .E8 :=
  Exc1.fiveTwoLayer_of_oddLieA5For (by decide)
    (C5Exc.oddLieA5For_E8 CatLeafProof.lieOrderFormulasInput)

end CFSG.ComponentClassification.SolMax.FiveCat.TwoL5
