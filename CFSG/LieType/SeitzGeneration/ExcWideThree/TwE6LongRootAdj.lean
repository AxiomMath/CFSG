module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootOps

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

theorem Psi.e6HighestRoot_idx_one : e6HighestRoot (e6Idx 1) = 2 := by decide

theorem Psi.degOne_apply {γ : Fin TwistTag.E6.tag.rank → ℤ} (h : γ ∈ degOneRoots) :
    γ (e6Idx 1) = 1 := by
  simpa [degOneRoots] using (Finset.mem_filter.1 h).2

theorem Psi.e6_degNegOne_aux : ∀ μ ∈ rootFinset TwistTag.E6.tag, μ (e6Idx 1) = -1 →
    μ + e6HighestRoot ∈ degOneRoots := by
  decide +kernel

theorem Psi.add_highest_mem_degOne
    {μ : Fin TwistTag.E6.tag.rank → ℤ} (hμ : IsRoot TwistTag.E6.tag μ) (h : μ (e6Idx 1) = -1) :
    μ + e6HighestRoot ∈ degOneRoots :=
  e6_degNegOne_aux μ (mem_rootFinset.2 hμ) h

theorem Psi.isRoot_sub_highest (γ : Dr) :
    IsRoot TwistTag.E6.tag (γ.1 - e6HighestRoot) :=
  mem_rootFinset.1 (sub_e6HighestRoot_mem γ.1 γ.2)

theorem Psi.sub_highest_apply_one (γ : Dr) : (γ.1 - e6HighestRoot) (e6Idx 1) = -1 := by
  rw [Pi.sub_apply, degOne_apply γ.2, e6HighestRoot_idx_one]
  norm_num

theorem Psi.isRoot_neg_highest :
    IsRoot TwistTag.E6.tag (-e6HighestRoot) :=
  IsRoot.neg isRoot_e6HighestRoot

@[expose] def Psi.lab (γ : Dr) : Label TwistTag.E6.tag :=
  Sum.inr ⟨γ.1 - e6HighestRoot, isRoot_sub_highest γ⟩

@[expose] def Psi.lab0 : Label TwistTag.E6.tag :=
  Sum.inr ⟨-e6HighestRoot, isRoot_neg_highest⟩

@[expose] def Psi.v0 (K : Type) [Field K] : RootModule TwistTag.E6.tag K :=
  rootVec TwistTag.E6.tag K (-e6HighestRoot)

theorem Psi.v0_eq (K : Type) [Field K] :
    v0 K = Finsupp.single lab0 1 :=
  rootVec_eq_single_of_isRoot isRoot_neg_highest

theorem Psi.lab_ne_lab0 (γ : Dr) : lab γ ≠ lab0 := by
  intro h
  simp only [lab, lab0, Sum.inr.injEq, Subtype.mk.injEq] at h
  have h1 := congrFun h (e6Idx 1)
  simp only [Pi.sub_apply, Pi.neg_apply, degOne_apply γ.2] at h1
  have h2 : (1 : ℤ) = 0 := by linarith
  exact one_ne_zero h2

@[expose] def Psi.lblDeg (b : Label TwistTag.E6.tag) : ℤ := b.latticeWeight (e6Idx 1)

theorem Psi.lblDeg_lab (γ : Dr) : lblDeg (lab γ) = -1 :=
  sub_highest_apply_one γ

theorem Psi.lblDeg_lab0 : lblDeg lab0 = -2 := by
  simp [lblDeg, lab0, Label.latticeWeight, e6HighestRoot_idx_one]

variable (K : Type) [Field K]

@[expose] def Psi.piD : RootModule TwistTag.E6.tag K →ₗ[K] Rv K where
  toFun y γ := y (lab γ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open Psi

@[expose] def psi (z : ModGL TwistTag.E6.tag K) : Rv K :=
  Psi.piD K ((z : Module.End K (RootModule TwistTag.E6.tag K)) (Psi.v0 K))

variable {K}

theorem psi_apply (z : ModGL TwistTag.E6.tag K) (γ : Dr) :
    psi K z γ = (z : Module.End K (RootModule TwistTag.E6.tag K)) (Psi.v0 K) (Psi.lab γ) := rfl

theorem Psi.rootVec_apply_lab (ν : Fin TwistTag.E6.tag.rank → ℤ)
    (γ : Dr) :
    rootVec TwistTag.E6.tag K ν (lab γ) = if ν = γ.1 - e6HighestRoot then 1 else 0 := by
  unfold rootVec
  by_cases hν : IsRoot TwistTag.E6.tag ν
  · rw [dif_pos hν, lab, Finsupp.single_apply]
    simp
  · rw [dif_neg hν]
    have : ν ≠ γ.1 - e6HighestRoot := fun e => hν (e ▸ isRoot_sub_highest γ)
    simp [this]

theorem Psi.piD_rootVec (ν : Fin TwistTag.E6.tag.rank → ℤ) (γ : Dr) :
    piD K (rootVec TwistTag.E6.tag K ν) γ = if ν = γ.1 - e6HighestRoot then 1 else 0 :=
  rootVec_apply_lab ν γ

theorem Psi.hVec_apply_lab (l : Fin TwistTag.E6.tag.rank) (γ : Dr) :
    hVec TwistTag.E6.tag K l (lab γ) = 0 := by
  simp [hVec, lab]

theorem Psi.piD_hVec (l : Fin TwistTag.E6.tag.rank) :
    piD K (hVec TwistTag.E6.tag K l) = 0 := by
  ext γ
  exact hVec_apply_lab l γ

theorem Psi.piD_eq_zero_of_apply_eq_zero
    {y : RootModule TwistTag.E6.tag K} (h : ∀ γ, y (lab γ) = 0) : piD K y = 0 := by
  ext γ
  exact h γ

theorem psi_one : psi K (1 : ModGL TwistTag.E6.tag K) = 0 := by
  ext γ
  rw [psi_apply, Units.val_one, Module.End.one_apply, Psi.v0_eq, Finsupp.single_apply,
    if_neg (Psi.lab_ne_lab0 γ).symm]
  rfl

theorem Psi.psi_conj (g z : ModGL TwistTag.E6.tag K) (l : K)
    (A : Rv K →ₗ[K] Rv K)
    (h0 : ((g⁻¹ : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) (v0 K) =
      l • v0 K)
    (hπ : ∀ y, piD K ((g : Module.End K (RootModule TwistTag.E6.tag K)) y) = A (piD K y)) :
    psi K (g * z * g⁻¹) = l • A (psi K z) := by
  unfold psi
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, h0]
  simp only [map_smul, hπ]

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
