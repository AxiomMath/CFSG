module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeReduce
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverChevalley

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem statedClassicalModel_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n r e : ℕ}
    (ht : t ∈ classicalTags) (h : LieModel X t n r e) : StatedClassicalModel X t n r e :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

theorem chevalleyExceptionalModel_of_lieModel {X : Type} [Group X] {t : StatedLieTag}
    {n r e : ℕ} (ht : t ∈ chevalleyExceptionalTags) (h : LieModel X t n r e) :
    ChevalleyExceptionalModel X t r e :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h ht

theorem lieModel_unique {X Y : Type} [Group X] [Group Y] {t : StatedLieTag} {n r e : ℕ}
    (hr2 : r ≠ 2) (hFT : IsFundTag t) (hX : LieModel X t n r e) (hY : LieModel Y t n r e) :
    Nonempty (X ≃* Y) := by
  by_cases hcl : t ∈ classicalTags
  · exact statedClassicalModel_unique hr2 (statedClassicalModel_of_lieModel hcl hX)
      (statedClassicalModel_of_lieModel hcl hY)
  · have hch : t ∈ chevalleyExceptionalTags := by
      cases t <;> first | exact absurd (by decide) hcl | decide | exact hFT.elim
    exact chevalleyExceptionalModel_unique (chevalleyExceptionalModel_of_lieModel hch hX)
      (chevalleyExceptionalModel_of_lieModel hch hY)

theorem lieModelCentralCover : LieModelCentralCover := by
  intro t n r e hr hr2 hFT hadm X _ _ _ hX
  obtain ⟨-, hY⟩ := ModelFacts.modelClauseZero t n r e hr hFT hadm
  obtain ⟨E⟩ := lieModel_unique hr2 hFT hX hY
  refine ⟨E.symm.toMonoidHom.comp (QuotientGroup.mk' _), ?_, fun k hk => ?_⟩
  · exact E.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  · have h1 : E.symm (QuotientGroup.mk' (Subgroup.center (modelUniv t n r e hr).K) k) = 1 := hk
    rw [map_eq_one_iff _ E.symm.injective] at h1
    exact (QuotientGroup.eq_one_iff k).1 h1

end CFSG.ClassicalInvolution.Upgrade
