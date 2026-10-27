module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizer

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type*} [Field K]

@[expose] noncomputable def outerSwap : Equiv.Perm (Fin n) :=
  Equiv.Perm.extendDomain (Equiv.sumComm (Fin k) (Fin k)) P.outerEquiv

theorem outerSwap_supp (s : Fin k ⊕ Fin k) : (P.outerSwap) (P.supp s) = P.supp s.swap := by
  rw [← P.coe_outerEquiv s, outerSwap, Equiv.Perm.extendDomain_apply_image, P.coe_outerEquiv]
  rfl

theorem outerSwap_u (a : Fin k) : (P.outerSwap) (P.u a) = P.w a :=
  P.outerSwap_supp (Sum.inl a)

theorem outerSwap_w (a : Fin k) : (P.outerSwap) (P.w a) = P.u a :=
  P.outerSwap_supp (Sum.inr a)

theorem outerSwap_of_mem_free {i : Fin n} (hi : i ∈ P.free) : (P.outerSwap) i = i :=
  Equiv.Perm.extendDomain_apply_not_subtype _ _ fun h => P.not_mem_free_of_mem_outer h hi

theorem level_outerSwap (i : Fin n) : P.level ((P.outerSwap) i) = 2 - P.level i := by
  have h2 := P.level_le_two i
  rcases (by omega : P.level i = 0 ∨ P.level i = 1 ∨ P.level i = 2) with h | h | h
  · obtain ⟨a, rfl⟩ := P.level_eq_zero_iff.1 h
    rw [P.outerSwap_u, P.level_w]
    omega
  · rw [P.outerSwap_of_mem_free (P.mem_free.2 h)]
    omega
  · obtain ⟨a, rfl⟩ := P.level_eq_two_iff.1 h
    rw [P.outerSwap_w, P.level_u]
    omega

theorem outerSwap_outerSwap (i : Fin n) : (P.outerSwap) ((P.outerSwap) i) = i := by
  have h2 := P.level_le_two i
  rcases (by omega : P.level i = 0 ∨ P.level i = 1 ∨ P.level i = 2) with h | h | h
  · obtain ⟨a, rfl⟩ := P.level_eq_zero_iff.1 h
    rw [P.outerSwap_u, P.outerSwap_w]
  · rw [P.outerSwap_of_mem_free (P.mem_free.2 h), P.outerSwap_of_mem_free (P.mem_free.2 h)]
  · obtain ⟨a, rfl⟩ := P.level_eq_two_iff.1 h
    rw [P.outerSwap_w, P.outerSwap_u]

theorem outerSwap_mul_self : P.outerSwap * P.outerSwap = 1 :=
  Equiv.ext P.outerSwap_outerSwap

theorem outerSwap_symm : P.outerSwap.symm = P.outerSwap :=
  Equiv.ext fun i => by rw [Equiv.symm_apply_eq, P.outerSwap_outerSwap]

theorem outerSwap_mem_free_iff {i : Fin n} : (P.outerSwap) i ∈ P.free ↔ i ∈ P.free := by
  rw [P.mem_free, P.mem_free, P.level_outerSwap]
  have := P.level_le_two i
  omega

variable (K) in
@[expose] noncomputable def outerSwapGL : GL (Fin n) K where
  val := P.outerSwap.permMatrix K
  inv := P.outerSwap.permMatrix K
  val_inv := by rw [← Matrix.permMatrix_mul, P.outerSwap_mul_self, Matrix.permMatrix_one]
  inv_val := by rw [← Matrix.permMatrix_mul, P.outerSwap_mul_self, Matrix.permMatrix_one]

theorem outerSwapGL_mul_mul_inv (M : Matrix (Fin n) (Fin n) K) :
    (P.outerSwapGL K : Matrix (Fin n) (Fin n) K) * M *
        ((P.outerSwapGL K)⁻¹ : GL (Fin n) K) = M.submatrix P.outerSwap P.outerSwap := by
  change P.outerSwap.toPEquiv.toMatrix * M * P.outerSwap.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix,
    P.outerSwap_symm]
  rfl

theorem fieldAut_mem_radicalP (σ : K ≃+* K) {x : projectiveSL n K} (hx : x ∈ P.radicalP K) :
    fieldAut n K σ x ∈ P.radicalP K := by
  obtain ⟨r, hr, rfl⟩ := hx
  rw [fieldAut_proj]
  refine Subgroup.mem_map_of_mem _ fun i j hij => ?_
  change σ ((r : Matrix (Fin n) (Fin n) K) i j) = _
  rw [hr i j hij]
  by_cases h : i = j
  · rw [h, one_apply_eq, map_one]
  · rw [one_apply_ne h, map_zero]

theorem graphTwist_mem_radicalP (σ : K ≃+* K) {x : projectiveSL n K} (hx : x ∈ P.radicalP K) :
    (conjAut n K (P.outerSwapGL K) * fieldAut n K σ * dualAut n K) x ∈ P.radicalP K := by
  obtain ⟨r, hr, rfl⟩ := hx
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj]
  refine Subgroup.mem_map_of_mem _ fun i j hij => ?_
  rw [coe_slConjugation, outerSwapGL_mul_mul_inv, submatrix_apply]
  have hri : r⁻¹ ∈ P.radical K := inv_mem hr
  have hle : P.level ((P.outerSwap) i) ≤ P.level ((P.outerSwap) j) := by
    rw [P.level_outerSwap, P.level_outerSwap]
    omega
  change σ (((r⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    ((P.outerSwap) j) ((P.outerSwap) i)) = _
  rw [hri _ _ hle]
  by_cases h : i = j
  · rw [h, one_apply_eq, one_apply_eq, map_one]
  · rw [one_apply_ne (fun h' => h (P.outerSwap.injective h').symm), one_apply_ne h, map_zero]

omit P in
theorem blockMatrix_map (I : Finset (Fin n)) (A : Matrix I I K) (f : K →+* K) :
    (blockMatrix I A).map f = blockMatrix I (A.map f) := by
  ext i j
  rw [map_apply, blockMatrix_apply, blockMatrix_apply]
  split_ifs with h
  · rfl
  · by_cases hij : i = j
    · rw [hij, one_apply_eq, map_one]
    · rw [one_apply_ne hij, map_zero]

omit P in
theorem blockMatrix_transpose (I : Finset (Fin n)) (A : Matrix I I K) :
    (blockMatrix I A).transpose = blockMatrix I A.transpose := by
  ext i j
  rw [transpose_apply, blockMatrix_apply, blockMatrix_apply]
  by_cases h : j ∈ I ∧ i ∈ I
  · rw [dite_eq_left h, dite_eq_left ⟨h.2, h.1⟩]
    rfl
  · rw [dite_eq_right h, dite_eq_right fun h' => h ⟨h'.2, h'.1⟩, one_apply, one_apply]
    by_cases hij : i = j
    · rw [ite_eq_left hij.symm, ite_eq_left hij]
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]

theorem blockMatrix_submatrix_outerSwap (A : Matrix P.free P.free K) :
    (blockMatrix P.free A).submatrix P.outerSwap P.outerSwap = blockMatrix P.free A := by
  ext i j
  rw [submatrix_apply, blockMatrix_apply, blockMatrix_apply]
  by_cases h : i ∈ P.free ∧ j ∈ P.free
  · have h' : (P.outerSwap) i ∈ P.free ∧ (P.outerSwap) j ∈ P.free :=
      ⟨P.outerSwap_mem_free_iff.2 h.1, P.outerSwap_mem_free_iff.2 h.2⟩
    rw [dite_eq_left h', dite_eq_left h]
    congr 1
    · exact Subtype.ext (P.outerSwap_of_mem_free h.1)
    · exact Subtype.ext (P.outerSwap_of_mem_free h.2)
  · have h' : ¬ ((P.outerSwap) i ∈ P.free ∧ (P.outerSwap) j ∈ P.free) := fun h' =>
      h ⟨P.outerSwap_mem_free_iff.1 h'.1, P.outerSwap_mem_free_iff.1 h'.2⟩
    rw [dite_eq_right h', dite_eq_right h]
    simp only [one_apply, P.outerSwap.injective.eq_iff]

omit P in
theorem fieldAut_proj_blockEmbed (I : Finset (Fin n)) (σ : K ≃+* K)
    (Y : SpecialLinearGroup I K) :
    fieldAut n K σ (proj n K (blockEmbed I Y)) =
      proj n K (blockEmbed I (SpecialLinearGroup.map σ.toRingHom Y)) := by
  rw [fieldAut_proj]
  congr 1
  exact Subtype.ext (blockMatrix_map I _ _)

theorem graphTwist_proj_blockEmbed (σ : K ≃+* K) (Y : SpecialLinearGroup P.free K) :
    (conjAut n K (P.outerSwapGL K) * fieldAut n K σ * dualAut n K)
        (proj n K (blockEmbed P.free Y)) =
      proj n K (blockEmbed P.free (SpecialLinearGroup.map σ.toRingHom (Y⁻¹).transpose)) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, outerSwapGL_mul_mul_inv, ← map_inv]
  change ((blockMatrix P.free ((Y⁻¹ : SpecialLinearGroup P.free K) :
    Matrix P.free P.free K)).transpose.map σ.toRingHom).submatrix P.outerSwap P.outerSwap = _
  rw [blockMatrix_transpose, blockMatrix_map, blockMatrix_submatrix_outerSwap]
  rfl

end InvPlacement

end CFSG.SeitzReduction.LinearPilot
