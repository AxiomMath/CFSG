module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm29

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

@[expose] def FooteSolomonMaximalStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → IsSimpleGroup G →
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) →
    ∀ A ∈ footeFamilyOf L, IsSolomonMaximal A

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_ne_mul_of_footeCounterexample {t : G} {L : Subgroup G}
    (hce : FooteCounterexample G t L) : ∃ u ∈ L, ∃ v ∈ L, u * v ≠ v * u := by
  obtain ⟨⟨-, -, ⟨-, hLt, hLpc⟩, -, -, -⟩, -⟩ := hce
  obtain ⟨u, v, huv⟩ :=
    exists_mul_ne_mul_of_isQuasisimple (isQuasisimple_quotient_of_isPComponent hLt hLpc)
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  refine ⟨u', u'.2, v', v'.2, fun h => huv ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, show u' * v' = v' * u' from Subtype.ext h]

theorem not_oddLieType_of_footeCounterexample [IsSimpleGroup G] {t : G} {L : Subgroup G}
    (hce : FooteCounterexample G t L) : ¬ Blueprint.OddLieType G := by
  intro hodd
  obtain ⟨u, hu, v, hv, huv⟩ := exists_mul_ne_mul_of_footeCounterexample hce
  obtain ⟨⟨-, -, ⟨ht, -, -⟩, -, -, -⟩, hcon⟩ := hce
  have hLne : L ≠ ⊥ := by
    rintro rfl
    rw [mem_bot] at hu hv
    exact huv (by rw [hu, hv])
  have hA : conjClosure L (pLayer G 2) = ⊤ := by
    rw [pLayer_two_eq_top_of_isSimpleGroup ⟨u, v, huv⟩ ht, conjClosure_top_eq_top hLne]
  rw [hA] at hcon
  have : IsSimpleGroup ↥(⊤ : Subgroup G) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).isSimpleGroup
  exact hcon (footeConclusion_of_oddLieType
    ⟨⟨u, mem_top u⟩, ⟨v, mem_top v⟩, fun h => huv (congrArg Subtype.val h)⟩
    ((ClassicalInvolution.oddLieType_congr Subgroup.topEquiv).2 hodd))

theorem footeSolomonFamilyInput_of_maximalStep (hA : Sol76.AschbacherRankOneInput)
    (hstep : FooteSolomonMaximalStep) : FooteSolomonFamilyInput := by
  intro G _ _ t L hmin hce hsimp hrank2 A hAF
  have htop : GeneralizedFitting.subgroup G = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup G) := eF.isSimpleGroup
  obtain ⟨u, -, v, -, huv⟩ := exists_mul_ne_mul_of_footeCounterexample hce
  have hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a := by
    refine ⟨eF.symm u, eF.symm v, fun h => huv ?_⟩
    have h1 := congrArg eF h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  have hoF : ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) := fun hodd =>
    not_oddLieType_of_footeCounterexample hce ((ClassicalInvolution.oddLieType_congr eF).1 hodd)
  exact Sol76.mem_solomonKStar_of_aschbacher hA hsF hnF hoF
    (hstep G t L hmin hce hsimp hrank2 A hAF)

end CFSG.ComponentClassification.FooteLit
