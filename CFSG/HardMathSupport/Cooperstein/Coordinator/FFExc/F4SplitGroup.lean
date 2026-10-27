module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitTables
public import CFSG.LieType.Steinberg.Minuscule.Group

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule Matrix

variable (hV : e6Data.Valid) (K : Type*) [Field K]

@[expose] def gen (α : Fin Tag.E6.rank → ℤ) (c : K) : hV.minGroup K :=
  if graphRoot α = α then hV.xm K α c else hV.xm K α c * hV.xm K (graphRoot α) c

@[expose] def F4in27 : Subgroup (hV.minGroup K) :=
  Subgroup.closure {g | ∃ α, IsRoot Tag.E6 α ∧ ∃ c, g = gen hV K α c}

variable {K}

theorem gen_mem_F4in27 (α : Fin Tag.E6.rank → ℤ) (hα : IsRoot Tag.E6 α) (c : K) :
    gen hV K α c ∈ F4in27 hV K :=
  Subgroup.subset_closure ⟨α, hα, c, rfl⟩

section Matrix

variable [CharP K 2]

@[expose] def rho (g : hV.minGroup K) : Matrix Ix Ix K :=
  LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne (hV.endo K g)

theorem rho_mul (g h : hV.minGroup K) : rho hV (g * h) = rho hV g * rho hV h := by
  unfold rho
  rw [MinData.Valid.endo_mul, LinearMap.toMatrix_mul]

theorem rho_one : rho hV (1 : hV.minGroup K) = 1 := by
  unfold rho
  rw [MinData.Valid.endo_one, LinearMap.toMatrix_one]

theorem rho_inv_mul (g : hV.minGroup K) : rho hV g⁻¹ * rho hV g = 1 := by
  rw [← rho_mul, inv_mul_cancel, rho_one]

theorem rho_mul_inv (g : hV.minGroup K) : rho hV g * rho hV g⁻¹ = 1 := by
  rw [← rho_mul, mul_inv_cancel, rho_one]

theorem toMatrix_E (k : ℕ) (hk : k < 72) :
    LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne (e6Data.E K k) =
      (Em2 k).map (cast2 K) := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.map_apply]
  simp only [Finsupp.coe_basisSingleOne, MinData.E, toEnd_single, Finsupp.basisSingleOne_repr,
    LinearEquiv.refl_apply, Em2, tgt_eq k hk j]
  unfold digVec
  have h2 : ((-1 : K) ^ dig (e6Data.op k) j) = 1 := by
    rw [CharTwo.neg_eq (1 : K), one_pow]
  by_cases h : 2 ≤ dig (e6Data.op k) j ∧ dig (e6Data.op k) j / 2 - 1 < e6Data.d
  · rw [dite_eq_left h, h2, one_smul, Finsupp.single_apply]
    by_cases h3 : dig (e6Data.op k) j / 2 - 1 = i.val
    · rw [ite_eq_left (Fin.ext h3), ite_eq_left (by omega), map_one]
    · rw [ite_eq_right (fun h4 => h3 (congrArg Fin.val h4)), ite_eq_right (by omega), map_zero]
  · rw [dite_eq_right h, ite_eq_right, map_zero]
    · rfl
    · intro h4
      exact h ⟨by omega, by have := i.2; omega⟩

theorem rho_xm (k : ℕ) (hk : k < 72) (c : K) :
    rho hV (hV.xm K (e6root k) c) = 1 + c • (Em2 k).map (cast2 K) := by
  have hlen : k < Tag.E6.rootCertificate.roots.length := hk
  unfold rho
  rw [MinData.Valid.endo_xm, map_add, map_smul, LinearMap.toMatrix_one]
  unfold e6root
  rw [MinData.rootOp_root hlen, toMatrix_E k hk]

end Matrix

section Invariants

variable [CharP K 2]

@[expose] def s3K (K : Type*) [Field K] [CharP K 2] : Ix → K := cast2 K ∘ s3Z

theorem inv_gen_root (k : ℕ) (hk : k < 72) (c : K) :
    rho hV (gen hV K (e6root k) c) *ᵥ s3K K = s3K K ∧
      s3K K ᵥ* rho hV (gen hV K (e6root k) c) = s3K K := by
  have hchk := f_fix_checks k hk
  unfold gen
  by_cases hfix : graphRoot (e6root k) = e6root k
  · rw [ite_eq_left hfix, rho_xm hV k hk]
    obtain ⟨h1, h2⟩ := hchk.1 hfix
    have h1' : (Em2 k).map (cast2 K) *ᵥ s3K K = 0 := by
      unfold s3K; rw [map_mulVec', h1]; exact comp_zero'
    have h2' : s3K K ᵥ* (Em2 k).map (cast2 K) = 0 := by
      unfold s3K; rw [map_vecMul', h2]; exact comp_zero'
    refine ⟨?_, ?_⟩
    · rw [add_mulVec, one_mulVec, smul_mulVec, h1', smul_zero, add_zero]
    · rw [vecMul_add, vecMul_one, vecMul_smul, h2', smul_zero, add_zero]
  · rw [ite_eq_right hfix, graphRoot_root k hk, rho_mul, rho_xm hV k hk, rho_xm hV _ (gamK_lt k hk)]
    obtain ⟨h1, h2, h3, h4⟩ := hchk.2 hfix
    have h1' : ((Em2 k).map (cast2 K) + (Em2 (gamK k)).map (cast2 K)) *ᵥ s3K K = 0 := by
      unfold s3K; rw [← Matrix.map_add _ (map_add (cast2 K)), map_mulVec', h1]; exact comp_zero'
    have h2' : (Em2 k).map (cast2 K) *ᵥ ((Em2 (gamK k)).map (cast2 K) *ᵥ s3K K) = 0 := by
      unfold s3K; rw [map_mulVec', map_mulVec', h2]; exact comp_zero'
    have h3' : s3K K ᵥ* ((Em2 k).map (cast2 K) + (Em2 (gamK k)).map (cast2 K)) = 0 := by
      unfold s3K; rw [← Matrix.map_add _ (map_add (cast2 K)), map_vecMul', h3]; exact comp_zero'
    have h4' : (s3K K ᵥ* (Em2 k).map (cast2 K)) ᵥ* (Em2 (gamK k)).map (cast2 K) = 0 := by
      unfold s3K; rw [map_vecMul', map_vecMul', h4]; exact comp_zero'
    exact ⟨pair_mulVec _ _ _ c h1' h2', pair_vecMul _ _ _ c h3' h4'⟩

theorem inv_gen (α : Fin Tag.E6.rank → ℤ) (hα : IsRoot Tag.E6 α) (c : K) :
    rho hV (gen hV K α c) *ᵥ s3K K = s3K K ∧ s3K K ᵥ* rho hV (gen hV K α c) = s3K K := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq Tag.E6.rootCertificate_check hα
  exact inv_gen_root hV k hk c

theorem inv_of_mem_F4in27 {g : hV.minGroup K} (hg : g ∈ F4in27 hV K) :
    rho hV g *ᵥ s3K K = s3K K ∧ s3K K ᵥ* rho hV g = s3K K := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, c, rfl⟩ := hx
    exact inv_gen hV α hα c
  | one => rw [rho_one, one_mulVec, vecMul_one]; exact ⟨rfl, rfl⟩
  | mul x y _ _ hx hy =>
    rw [rho_mul, ← mulVec_mulVec, hy.1, hx.1, ← vecMul_vecMul, hx.2, hy.2]
    exact ⟨rfl, rfl⟩
  | inv x _ hx =>
    refine ⟨?_, ?_⟩
    · calc rho hV x⁻¹ *ᵥ s3K K = rho hV x⁻¹ *ᵥ (rho hV x *ᵥ s3K K) := by rw [hx.1]
        _ = s3K K := by rw [mulVec_mulVec, rho_inv_mul, one_mulVec]
    · calc s3K K ᵥ* rho hV x⁻¹ = (s3K K ᵥ* rho hV x) ᵥ* rho hV x⁻¹ := by rw [hx.2]
        _ = s3K K := by rw [vecMul_vecMul, rho_mul_inv, vecMul_one]

end Invariants

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
