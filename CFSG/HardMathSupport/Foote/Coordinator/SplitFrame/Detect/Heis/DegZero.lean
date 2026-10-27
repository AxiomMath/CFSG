module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Defs
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.RankThree.PartOne.KE.ConjRootSpan

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K]

theorem rootSubgroup_smul_le_of_mem {M : Subgroup (ModGL τ K)} {w : WeylGroup τ}
    (hw : canonicalRep (coxeterSystem τ) K w ∈ M) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    (hδM : rootSubgroup τ K δ ≤ M) : rootSubgroup τ K (w • δ) ≤ M := by
  rw [← CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup (L := K) w hδ]
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem hw (hδM hx)) (inv_mem hw)

theorem rootSubgroup_single_le_Lθ {j : Fin τ.rank} (hj : j ∈ Jθ τ) :
    rootSubgroup τ K (Pi.single j 1) ≤ Lθ τ K :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_single]
    exact xUnit_mem_parabolicLevi hj c)

theorem rootSubgroup_neg_single_le_Lθ {j : Fin τ.rank} (hj : j ∈ Jθ τ) :
    rootSubgroup τ K (-Pi.single j 1) ≤ Lθ τ K :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_neg_single]
    exact yUnit_mem_parabolicLevi hj c)

theorem rootSubgroup_le_Lθ_of_deg_zero {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (h0 : γ (iθ τ) = 0) : rootSubgroup τ K γ ≤ Lθ τ K := by
  have hγJ : γ ∈ parabolicRoots τ (Jθ τ) := by
    refine ⟨hγ, fun i hi => ?_⟩
    have : i = iθ τ := by simpa [Jθ] using hi
    rw [this]
    exact h0
  rcases IsRoot.height_pos_or_neg hγ with hpos | hneg
  · obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ γ rfl ⟨hγJ, hγ, hpos⟩
    rw [← hwj]
    exact rootSubgroup_smul_le_of_mem (canonicalRep_mem_parabolicLevi hw)
      (isRoot_single τ j) (rootSubgroup_single_le_Lθ hj)
  · have hneg' : -γ ∈ parabolicPosRoots τ (Jθ τ) :=
      ⟨⟨IsRoot.neg hγ, fun i hi => by rw [Pi.neg_apply, hγJ.2 i hi, neg_zero]⟩,
        IsRoot.neg hγ, by rw [height_neg]; omega⟩
    obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ (-γ) rfl hneg'
    have e : γ = w • (-Pi.single j 1 : Fin τ.rank → ℤ) := by rw [smul_neg, hwj, neg_neg]
    rw [e]
    exact rootSubgroup_smul_le_of_mem (canonicalRep_mem_parabolicLevi hw)
      (isRoot_neg_single τ j) (rootSubgroup_neg_single_le_Lθ hj)

theorem pinnedX_mem_Lθ_of_deg_zero {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (h0 : γ (iθ τ) = 0)
    (t : K) : pinnedX τ K γ t ∈ Lθ τ K :=
  rootSubgroup_le_Lθ_of_deg_zero hγ h0 (mem_rootSubgroup.2 ⟨t, rfl⟩)

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
