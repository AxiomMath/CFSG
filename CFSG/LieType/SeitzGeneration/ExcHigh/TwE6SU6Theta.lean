module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Levi
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoFrame

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcHigh
open scoped MatrixGroups

theorem theta_a5_check : ∀ k : Fin 5,
    RootOps.isRootB TwistTag.E6.tag (frameRoot 3) = true ∧
      RootOps.isRootB TwistTag.E6.tag (Pi.single (a5Node k) 1) = true ∧
      iform (frameRoot 3) (Pi.single (a5Node k) 1) = 0 ∧
      RootOps.isRootB TwistTag.E6.tag (frameRoot 3 + Pi.single (a5Node k) 1) = false ∧
      RootOps.isRootB TwistTag.E6.tag (frameRoot 3 - Pi.single (a5Node k) 1) = false := by
  decide +kernel

section Commute


variable {K : Type} [Field K]

theorem commute_frameHom_three_gen (σ : K →+* K)
    (A : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K)))
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ a5Gens K) :
    ((frameHom σ 3 A : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) * g =
      g * ((frameHom σ 3 A : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) := by
  have hx := frameHom_mem_rootPair σ 3 A
  simp only [a5Gens, Set.mem_iUnion, Set.mem_union, Set.mem_range] at hg
  obtain ⟨k, ⟨c, rfl⟩ | ⟨c, rfl⟩⟩ := hg
  · obtain ⟨h1, h2, h3, h4, h5⟩ := theta_a5_check k
    have hy : (xUnit TwistTag.E6.tag K (a5Node k) c : ModGL TwistTag.E6.tag K) ∈
        rootSubgroup TwistTag.E6.tag K (Pi.single (a5Node k) 1) ⊔
          rootSubgroup TwistTag.E6.tag K (-(Pi.single (a5Node k) 1)) :=
      Subgroup.mem_sup_left (by
        rw [← pinnedX_single]
        exact Subgroup.subset_closure ⟨c, rfl⟩)
    exact commute_of_mem_rootPair_of_check h1 h2 h3 h4 h5 hx hy
  · obtain ⟨h1, h2, h3, h4, h5⟩ := theta_a5_check k
    have hy : (yUnit TwistTag.E6.tag K (a5Node k) c : ModGL TwistTag.E6.tag K) ∈
        rootSubgroup TwistTag.E6.tag K (Pi.single (a5Node k) 1) ⊔
          rootSubgroup TwistTag.E6.tag K (-(Pi.single (a5Node k) 1)) :=
      Subgroup.mem_sup_right (by
        rw [← pinnedX_neg_single]
        exact Subgroup.subset_closure ⟨c, rfl⟩)
    exact commute_of_mem_rootPair_of_check h1 h2 h3 h4 h5 hx hy

theorem commute_frameHom_three (σ : K →+* K)
    (A : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K)))
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ Subgroup.closure (a5Gens K)) :
    ((frameHom σ 3 A : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) * g =
      g * ((frameHom σ 3 A : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) := by
  have hle : Subgroup.closure (a5Gens K) ≤
      Subgroup.centralizer ({((frameHom σ 3 A : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K)} : Set (ModGL TwistTag.E6.tag K)) := by
    rw [Subgroup.closure_le]
    intro h hh
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff.1 hy]
    exact commute_frameHom_three_gen σ A hh
  exact Subgroup.mem_centralizer_iff.1 (hle hg) _ (Set.mem_singleton _)

end Commute

end CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
