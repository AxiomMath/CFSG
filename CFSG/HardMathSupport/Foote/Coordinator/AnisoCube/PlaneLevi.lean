module

public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.FrameLevi
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.Skeleton
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SeitzGeneration.HyperExParabolic
public import CFSG.LieType.SeitzGeneration.HyperLinear
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

public noncomputable section

open CFSG.HardMathSupport.Malle.SeitzCube
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A (m := 2)) ∅

theorem parabolicLevi_mono {τ : Tag} {K : Type} [Field K]
    {A B : Set (Fin τ.rank)} (h : A ⊆ B) :
    parabolicLevi τ K A ≤ parabolicLevi τ K B := by
  refine sup_le_sup_left (Subgroup.closure_mono ?_) _
  rintro g ⟨j, hj, c, hc⟩
  exact ⟨j, h hj, c, hc⟩


theorem plane_le_parabolicLevi_E6 (K : Type) [Field K]
    (ψ : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K)
    (hψ : ∀ i : Fin 3, ∀ γ : Fin 2 → ℤ, γ ∈ RA2 → ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      ((ψ i (CFSG.LieType.Steinberg.SL.x 2 K γ c) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        pinnedX Tag.E6 K (e6A2Frame i γ) (ε * c))
    (g : SL(3, K)) :
    (plane ψ g).map (adjointGroup Tag.E6 K).subtype ≤
      parabolicLevi Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) := by
  rw [Subgroup.map_le_iff_le_comap]
  unfold plane
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (rfl | rfl)
  · have h0 := range_le_parabolicLevi_E6 K ψ hψ 0 g
    exact parabolicLevi_mono Set.subset_union_left h0
  · have h1 := range_le_parabolicLevi_E6 K ψ hψ 1 g
    exact parabolicLevi_mono Set.subset_union_right h1

theorem plane_le_normalizer_parabolicRadical_E6 (K : Type) [Field K]
    (ψ : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K)
    (hψ : ∀ i : Fin 3, ∀ γ : Fin 2 → ℤ, γ ∈ RA2 → ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      ((ψ i (CFSG.LieType.Steinberg.SL.x 2 K γ c) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        pinnedX Tag.E6 K (e6A2Frame i γ) (ε * c))
    (g : SL(3, K)) :
    ∀ x ∈ plane ψ g,
      ((x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
        Subgroup.normalizer
          (parabolicRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) :
            Set (ModGL Tag.E6 K)) := by
  intro x hx
  have hL : ((x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
      parabolicLevi Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) :=
    plane_le_parabolicLevi_E6 K ψ hψ g ⟨x, hx, rfl⟩
  exact parabolicSubgroup_le_normalizer_parabolicRadical _
    (parabolicLevi_le_parabolicSubgroup _ hL)

end

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
