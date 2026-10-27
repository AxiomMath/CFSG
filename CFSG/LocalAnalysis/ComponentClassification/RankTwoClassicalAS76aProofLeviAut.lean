module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviProj
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Transvections

variable {K : Type} [Field K] {n : ℕ}

@[expose] def trn (i j : Fin n) (hij : i ≠ j) (a : K) : SpecialLinearGroup (Fin n) K :=
  ⟨1 + single i j a, det_transvection_of_ne i j hij a⟩

theorem coe_trn (i j : Fin n) (hij : i ≠ j) (a : K) :
    ((trn i j hij a : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + single i j a :=
  rfl

theorem map_trn (τ : K →+* K) (i j : Fin n) (hij : i ≠ j) (a : K) :
    SpecialLinearGroup.map τ (trn i j hij a) = trn i j hij (τ a) := by
  apply Subtype.ext
  change τ.mapMatrix (1 + single i j a) = 1 + single i j (τ a)
  rw [map_add, map_one]
  congr 1
  ext x y
  rw [RingHom.mapMatrix_apply, map_apply, single_apply, single_apply]
  split_ifs <;> simp

theorem transpose_trn (i j : Fin n) (hij : i ≠ j) (a : K) :
    (trn i j hij a).transpose = trn j i hij.symm a := by
  apply Subtype.ext
  change (1 + single i j a)ᵀ = 1 + single j i a
  rw [transpose_add, transpose_one, transpose_single]

theorem trn_mul_self [CharP K 2] (i j : Fin n) (hij : i ≠ j) (a : K) :
    trn i j hij a * trn i j hij a = 1 := by
  apply Subtype.ext
  change (1 + single i j a) * (1 + single i j a) = 1
  have hEE : single i j a * single i j a = 0 := by simp [hij.symm]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, hEE, add_zero, add_assoc, ← single_add, CharTwo.add_self_eq_zero,
    single_zero, add_zero]

theorem trn_sq [CharP K 2] (i j : Fin n) (hij : i ≠ j) (a : K) : trn i j hij a ^ 2 = 1 := by
  rw [sq, trn_mul_self]

theorem inv_transpose_trn [CharP K 2] (i j : Fin n) (hij : i ≠ j) (a : K) :
    (trn i j hij a)⁻¹.transpose = trn j i hij.symm a := by
  rw [inv_eq_of_mul_eq_one_right (trn_mul_self i j hij a), transpose_trn]

theorem map_eq_self {τ : K ≃+* K} (hτ : ∀ a, τ a = a) (g : SpecialLinearGroup (Fin n) K) :
    SpecialLinearGroup.map τ.toRingHom g = g := by
  apply Subtype.ext
  ext i j
  exact hτ _

end Transvections

section Proj

variable {K : Type} [Field K] {n : ℕ}

theorem eq_one_of_mem_scalars_of_sq [CharP K 2] {u : SpecialLinearGroup (Fin n) K}
    (hu : u ∈ scalars n K) (h2 : u ^ 2 = 1) : u = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hu
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
  · exact Subsingleton.elim _ _
  have h3 := congrArg (fun x : Matrix (Fin n) (Fin n) K => x i i) (congrArg Subtype.val h2)
  simp only [Matrix.SpecialLinearGroup.coe_pow, hc, scalar_apply, diagonal_pow,
    diagonal_apply_eq, Pi.pow_apply, Matrix.SpecialLinearGroup.coe_one, one_apply_eq] at h3
  have hc2 : (c : K) = 1 := by
    have h4 : ((c : K) - 1) ^ 2 = 0 := by
      rw [sub_sq, h3, mul_one, CharTwo.two_eq_zero, zero_mul, sub_zero, one_pow,
        CharTwo.add_self_eq_zero]
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)
  apply Subtype.ext
  rw [hc, hc2, map_one]
  rfl

theorem eq_of_proj_eq_of_sq [CharP K 2] {g t : SpecialLinearGroup (Fin n) K} (hg : g ^ 2 = 1)
    (ht : t ^ 2 = 1) (h : proj n K g = proj n K t) : g = t := by
  have hz : g * t⁻¹ ∈ scalars n K := by
    rw [← proj_eq_one_iff, map_mul, map_inv, h, mul_inv_cancel]
  have hzc : g * t⁻¹ ∈ center (SpecialLinearGroup (Fin n) K) := (scalars_eq_center n K).le hz
  have h2 : (g * t⁻¹) ^ 2 = 1 := by
    have hc : Commute (g * t⁻¹) t := (mem_center_iff.mp hzc t).symm
    have := hc.mul_pow 2
    rw [inv_mul_cancel_right, hg, ht, mul_one] at this
    exact this.symm
  have := eq_one_of_mem_scalars_of_sq hz h2
  rwa [mul_inv_eq_one] at this

theorem eq_of_mul_self_eq [CharP K 2] {a b : K} (h : a * a = b * b) : a = b := by
  refine frobenius_inj K 2 ?_
  rw [frobenius_def, frobenius_def, sq, sq, h]

theorem std_zero_proj (B : GL (Fin n) K) (τ : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    (conjAut n K B * fieldAut n K τ * dualAut n K ^ 0) (proj n K g) =
      proj n K (CatalogueBHigherLinearAction.slConjugation n K B
        (SpecialLinearGroup.map τ.toRingHom g)) := by
  rw [pow_zero, mul_one, MulAut.mul_apply, fieldAut_proj, conjAut_proj]

theorem std_one_proj (B : GL (Fin n) K) (τ : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    (conjAut n K B * fieldAut n K τ * dualAut n K ^ 1) (proj n K g) =
      proj n K (CatalogueBHigherLinearAction.slConjugation n K B
        (SpecialLinearGroup.map τ.toRingHom (g⁻¹).transpose)) := by
  rw [pow_one, MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj]

theorem mul_eq_mul_of_proj_eq [CharP K 2] (B : GL (Fin n) K) {u t : SpecialLinearGroup (Fin n) K}
    (hu : u ^ 2 = 1) (ht : t ^ 2 = 1)
    (h : proj n K (CatalogueBHigherLinearAction.slConjugation n K B u) = proj n K t) :
    (B : Matrix (Fin n) (Fin n) K) * u = t * B := by
  have h1 := eq_of_proj_eq_of_sq
    (by rw [← map_pow (CatalogueBHigherLinearAction.slConjugation n K B) u 2, hu, map_one]) ht h
  have h2 := congrArg Subtype.val h1
  rw [CatalogueBHigherLinearAction.slConjugation_matrix] at h2
  rw [← h2, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

theorem exists_scalar_of_conjAut_sq [CharP K 2] (B : GL (Fin n) K)
    (h : conjAut n K B * conjAut n K B = 1) :
    ∃ z : K, ((B * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = scalar (Fin n) z := by
  rw [← map_mul] at h
  obtain ⟨z, hz⟩ := mem_range_scalar_of_commute_single
    (M := ((B * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) fun i j hij => by
      have h1 := congrArg (fun α : MulAut (projectiveSL n K) => α (proj n K (trn i j hij 1))) h
      simp only [conjAut_proj, MulAut.one_apply] at h1
      have h2 := mul_eq_mul_of_proj_eq (B * B) (trn_sq i j hij 1) (trn_sq i j hij 1) h1
      rw [coe_trn, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h2
      exact (add_left_cancel h2).symm
  exact ⟨z, hz.symm⟩

theorem conjAut_eq_one_of_scalar (B : GL (Fin n) K) {c : K}
    (hB : (B : Matrix (Fin n) (Fin n) K) = scalar (Fin n) c) : conjAut n K B = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [CatalogueBHigherLinearAction.slConjugation_matrix]
  have hc : (B : Matrix (Fin n) (Fin n) K) * g = g * B := by
    rw [hB]
    exact scalar_commute c (fun _ => Commute.all _ _) _
  rw [hc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem fieldAut_eq_one {τ : K ≃+* K} (hτ : ∀ a, τ a = a) : fieldAut n K τ = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [fieldAut_proj, MulAut.one_apply, map_eq_self hτ]

end Proj

section Blocks

variable {K : Type} [Field K] {k : ℕ}

theorem map_blk (τ : K →+* K) (X : Matrix (Fin 2) (Fin 2) K) (S : Matrix (Fin k) (Fin k) K) :
    τ.mapMatrix (blk X S) = blk (τ.mapMatrix X) (τ.mapMatrix S) := by
  simp only [blk, coe_reindexAlgEquiv, RingHom.mapMatrix_apply, reindex_apply, ← submatrix_map,
    fromBlocks_map, Matrix.map_zero _ τ.map_zero]

theorem transpose_blk (X : Matrix (Fin 2) (Fin 2) K) (S : Matrix (Fin k) (Fin k) K) :
    (blk X S)ᵀ = blk Xᵀ Sᵀ := by
  rw [blk, blk, coe_reindexAlgEquiv, transpose_reindex, fromBlocks_transpose, transpose_zero,
    transpose_zero]

theorem blk_one_add (X : Matrix (Fin 2) (Fin 2) K) :
    blk (1 + X) (1 : Matrix (Fin k) (Fin k) K) = 1 + blk X 0 := by
  rw [← blk_one, blk_add, add_zero]

theorem map_blkSL₁ (τ : K →+* K) (X : SpecialLinearGroup (Fin 2) K) :
    SpecialLinearGroup.map τ (blkSL₁ X : SpecialLinearGroup (Fin (2 + k)) K) =
      blkSL₁ (SpecialLinearGroup.map τ X) := by
  apply Subtype.ext
  change τ.mapMatrix (blk (X : Matrix (Fin 2) (Fin 2) K) 1) = blk (τ.mapMatrix X) 1
  rw [map_blk, map_one]

theorem map_blkSL₂ (τ : K →+* K) (S : SpecialLinearGroup (Fin k) K) :
    SpecialLinearGroup.map τ (blkSL₂ S : SpecialLinearGroup (Fin (2 + k)) K) =
      blkSL₂ (SpecialLinearGroup.map τ S) := by
  apply Subtype.ext
  change τ.mapMatrix (blk 1 (S : Matrix (Fin k) (Fin k) K)) = blk 1 (τ.mapMatrix S)
  rw [map_blk, map_one]

theorem transpose_blkSL₁ (X : SpecialLinearGroup (Fin 2) K) :
    (blkSL₁ X : SpecialLinearGroup (Fin (2 + k)) K).transpose = blkSL₁ X.transpose := by
  apply Subtype.ext
  change (blk (X : Matrix (Fin 2) (Fin 2) K) 1)ᵀ = blk (X : Matrix (Fin 2) (Fin 2) K)ᵀ 1
  rw [transpose_blk, transpose_one]

theorem transpose_blkSL₂ (S : SpecialLinearGroup (Fin k) K) :
    (blkSL₂ S : SpecialLinearGroup (Fin (2 + k)) K).transpose = blkSL₂ S.transpose := by
  apply Subtype.ext
  change (blk 1 (S : Matrix (Fin k) (Fin k) K))ᵀ = blk 1 (S : Matrix (Fin k) (Fin k) K)ᵀ
  rw [transpose_blk, transpose_one]

@[expose] def swapM : Matrix (Fin 2) (Fin 2) K := single 0 1 1 + single 1 0 1

theorem swapM_mul_swapM : (swapM : Matrix (Fin 2) (Fin 2) K) * swapM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM, Matrix.mul_apply, single_apply]

theorem swapM_mul_single₀₁ :
    (swapM : Matrix (Fin 2) (Fin 2) K) * single 0 1 1 = single 1 0 1 * swapM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM, Matrix.mul_apply, single_apply]

theorem swapM_mul_single₁₀ :
    (swapM : Matrix (Fin 2) (Fin 2) K) * single 1 0 1 = single 0 1 1 * swapM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM, Matrix.mul_apply, single_apply]

theorem det_ne_zero_of_blk {B : GL (Fin (2 + k)) K} {X : Matrix (Fin 2) (Fin 2) K}
    {D : Matrix (Fin k) (Fin k) K} (hB : B.val = blk X D) : X.det ≠ 0 ∧ D.det ≠ 0 := by
  have h := ((Matrix.isUnit_iff_isUnit_det B.val).mp (Units.isUnit B)).ne_zero
  rw [hB, det_blk] at h
  exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

end Blocks

section Fix

variable {K : Type} [Field K] [CharP K 2] {k : ℕ}

omit [CharP K 2] in
theorem slConjugation_eq_of_mul_eq {n : ℕ} (B : GL (Fin n) K) {h h' : SpecialLinearGroup (Fin n) K}
    (hh : (B : Matrix (Fin n) (Fin n) K) * h = h' * B) :
    CatalogueBHigherLinearAction.slConjugation n K B h = h' := by
  apply Subtype.ext
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, hh, Matrix.mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem fix_barW_zero {B : GL (Fin (2 + k)) K} {τ : K ≃+* K}
    (hW : ∀ w ∈ barW K k,
      (conjAut (2 + k) K B * fieldAut (2 + k) K τ * dualAut (2 + k) K ^ 0) w = w) :
    (∀ a, τ a = a) ∧ ∃ (c : K) (D : Matrix (Fin k) (Fin k) K), c ≠ 0 ∧ B.val = blk (c • 1) D := by
  have key : ∀ (i j : Fin 2) (hij : i ≠ j) (a : K),
      B.val * blk (single i j (τ a)) 0 = blk (single i j a) 0 * B.val := by
    intro i j hij a
    have h := hW _ ⟨trn i j hij a, rfl⟩
    simp only [MonoidHom.comp_apply] at h
    rw [std_zero_proj, map_blkSL₁, map_trn] at h
    have h2 := mul_eq_mul_of_proj_eq B (by rw [← map_pow, trn_sq, map_one])
      (by rw [← map_pow, trn_sq, map_one]) h
    rw [coe_blkSL₁, coe_blkSL₁, coe_trn, coe_trn, blk_one_add, blk_one_add, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h2
    exact add_left_cancel h2
  have h01 := key 0 1 (by decide) 1
  have h10 := key 1 0 (by decide) 1
  rw [map_one] at h01 h10
  obtain ⟨c, D, hB⟩ := exists_blk_of_commute_single h01 h10
  have hc : c ≠ 0 := by
    rintro rfl
    exact (det_ne_zero_of_blk hB).1 (by rw [zero_smul, det_zero])
  refine ⟨fun a => ?_, c, D, hc, hB⟩
  have h := key 0 1 (by decide) a
  rw [hB, blk_mul, blk_mul] at h
  have h1 := congrFun (congrFun (blk_injective h).1 0) 1
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.smul_apply,
    single_apply_same, smul_eq_mul] at h1
  exact mul_left_cancel₀ hc h1

theorem fix_barW_one {B : GL (Fin (2 + k)) K} {τ : K ≃+* K}
    (hW : ∀ w ∈ barW K k,
      (conjAut (2 + k) K B * fieldAut (2 + k) K τ * dualAut (2 + k) K ^ 1) w = w) :
    (∀ a, τ a = a) ∧
      ∃ (c : K) (D : Matrix (Fin k) (Fin k) K), c ≠ 0 ∧ B.val = blk (c • swapM) D := by
  have key : ∀ (i j : Fin 2) (hij : i ≠ j) (a : K),
      B.val * blk (single j i (τ a)) 0 = blk (single i j a) 0 * B.val := by
    intro i j hij a
    have h := hW _ ⟨trn i j hij a, rfl⟩
    simp only [MonoidHom.comp_apply] at h
    rw [std_one_proj, ← map_inv, transpose_blkSL₁, inv_transpose_trn, map_blkSL₁, map_trn] at h
    have h2 := mul_eq_mul_of_proj_eq B (by rw [← map_pow, trn_sq, map_one])
      (by rw [← map_pow, trn_sq, map_one]) h
    rw [coe_blkSL₁, coe_blkSL₁, coe_trn, coe_trn, blk_one_add, blk_one_add, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h2
    exact add_left_cancel h2
  have h01 := key 0 1 (by decide) 1
  have h10 := key 1 0 (by decide) 1
  rw [map_one] at h01 h10
  set J : Matrix (Fin (2 + k)) (Fin (2 + k)) K := blk swapM 1 with hJ
  have hJJ : J * J = 1 := by rw [hJ, blk_mul, swapM_mul_swapM, Matrix.mul_one, blk_one]
  have hJ01 : J * blk (single 0 1 1) 0 = blk (single 1 0 1) 0 * J := by
    rw [hJ, blk_mul, blk_mul, swapM_mul_single₀₁, Matrix.mul_zero, Matrix.zero_mul]
  have hJ10 : J * blk (single 1 0 1) 0 = blk (single 0 1 1) 0 * J := by
    rw [hJ, blk_mul, blk_mul, swapM_mul_single₁₀, Matrix.mul_zero, Matrix.zero_mul]
  have c1 : B.val * J * blk (single 0 1 1) 0 = blk (single 0 1 1) 0 * (B.val * J) :=
    calc B.val * J * blk (single 0 1 1) 0 = B.val * (J * blk (single 0 1 1) 0) :=
          Matrix.mul_assoc _ _ _
      _ = B.val * blk (single 1 0 1) 0 * J := by rw [hJ01, Matrix.mul_assoc]
      _ = blk (single 0 1 1) 0 * (B.val * J) := by rw [h01, Matrix.mul_assoc]
  have c2 : B.val * J * blk (single 1 0 1) 0 = blk (single 1 0 1) 0 * (B.val * J) :=
    calc B.val * J * blk (single 1 0 1) 0 = B.val * (J * blk (single 1 0 1) 0) :=
          Matrix.mul_assoc _ _ _
      _ = B.val * blk (single 0 1 1) 0 * J := by rw [hJ10, Matrix.mul_assoc]
      _ = blk (single 1 0 1) 0 * (B.val * J) := by rw [h10, Matrix.mul_assoc]
  obtain ⟨c, D, hBJ⟩ := exists_blk_of_commute_single c1 c2
  have hB : B.val = blk (c • swapM) D :=
    calc B.val = B.val * J * J := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = blk (c • swapM) D := by
        rw [hBJ, hJ, blk_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one]
  have hc : c ≠ 0 := by
    rintro rfl
    exact (det_ne_zero_of_blk hB).1 (by rw [zero_smul, det_zero])
  refine ⟨fun a => ?_, c, D, hc, hB⟩
  have h := key 0 1 (by decide) a
  rw [hB, blk_mul, blk_mul] at h
  have h1 := congrFun (congrFun (blk_injective h).1 0) 0
  simp [swapM, Matrix.mul_apply, single_apply] at h1
  exact mul_left_cancel₀ hc (h1.trans (mul_comm a c))

theorem fix_barL_zero {B : GL (Fin (2 + k)) K} {τ : K ≃+* K} {X : Matrix (Fin 2) (Fin 2) K}
    {D : Matrix (Fin k) (Fin k) K} (hB : B.val = blk X D)
    (hL : ∀ l ∈ barL K k,
      (conjAut (2 + k) K B * fieldAut (2 + k) K τ * dualAut (2 + k) K ^ 0) l = l)
    (i j : Fin k) (hij : i ≠ j) : D * single i j 1 = single i j 1 * D := by
  have h := hL _ ⟨trn i j hij 1, rfl⟩
  simp only [MonoidHom.comp_apply] at h
  rw [std_zero_proj, map_blkSL₂, map_trn, map_one] at h
  have h2 := mul_eq_mul_of_proj_eq B (by rw [← map_pow, trn_sq, map_one])
    (by rw [← map_pow, trn_sq, map_one]) h
  rw [coe_blkSL₂, coe_trn, hB, blk_mul, blk_mul] at h2
  have h3 := (blk_injective h2).2
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h3
  exact add_left_cancel h3

theorem fix_barL_one {B : GL (Fin (2 + k)) K} {τ : K ≃+* K} {X : Matrix (Fin 2) (Fin 2) K}
    {D : Matrix (Fin k) (Fin k) K} (hB : B.val = blk X D)
    (hL : ∀ l ∈ barL K k,
      (conjAut (2 + k) K B * fieldAut (2 + k) K τ * dualAut (2 + k) K ^ 1) l = l)
    (i j : Fin k) (hij : i ≠ j) : D * single j i 1 = single i j 1 * D := by
  have h := hL _ ⟨trn i j hij 1, rfl⟩
  simp only [MonoidHom.comp_apply] at h
  rw [std_one_proj, ← map_inv, transpose_blkSL₂, inv_transpose_trn, map_blkSL₂, map_trn,
    map_one] at h
  have h2 := mul_eq_mul_of_proj_eq B (by rw [← map_pow, trn_sq, map_one])
    (by rw [← map_pow, trn_sq, map_one]) h
  rw [coe_blkSL₂, coe_blkSL₂, coe_trn, coe_trn, hB, blk_mul, blk_mul] at h2
  have h3 := (blk_injective h2).2
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h3
  exact add_left_cancel h3

theorem eq_one_of_fix_zero (hk : 1 ≤ k) {B : GL (Fin (2 + k)) K} {τ : K ≃+* K}
    (h2 : (conjAut (2 + k) K B * fieldAut (2 + k) K τ * dualAut (2 + k) K ^ 0) *
      (conjAut (2 + k) K B * fieldAut (2 + k) K τ * dualAut (2 + k) K ^ 0) = 1)
    (hW : ∀ w ∈ barW K k,
      (conjAut (2 + k) K B * fieldAut (2 + k) K τ * dualAut (2 + k) K ^ 0) w = w)
    (hL : ∀ l ∈ barL K k,
      (conjAut (2 + k) K B * fieldAut (2 + k) K τ * dualAut (2 + k) K ^ 0) l = l) :
    conjAut (2 + k) K B * fieldAut (2 + k) K τ * dualAut (2 + k) K ^ 0 = 1 := by
  obtain ⟨hτ, c, D, -, hB⟩ := fix_barW_zero hW
  obtain ⟨d, hd⟩ := mem_range_scalar_of_commute_single (M := D) fun i j hij =>
    (fix_barL_zero hB hL i j hij).symm
  rw [fieldAut_eq_one hτ, pow_zero, mul_one, mul_one] at h2 ⊢
  obtain ⟨z, hz⟩ := exists_scalar_of_conjAut_sq B h2
  rw [Units.val_mul, hB, blk_mul, scalar_eq_blk, ← hd] at hz
  obtain ⟨hz1, hz2⟩ := blk_injective hz
  have e1 : c * c = z := by
    have := congrFun (congrFun hz1 0) 0
    simpa [Matrix.smul_mul] using this
  have e2 : d * d = z := by
    have := congrFun (congrFun hz2 ⟨0, hk⟩) ⟨0, hk⟩
    simpa using this
  have hcd : c = d := eq_of_mul_self_eq (e1.trans e2.symm)
  refine conjAut_eq_one_of_scalar B (c := c) ?_
  rw [hB, scalar_eq_blk, ← hd, hcd, scalar_apply, ← smul_one_eq_diagonal]

theorem false_of_fix_one_of_three_le (hk : 3 ≤ k) {B : GL (Fin (2 + k)) K} {τ : K ≃+* K}
    (hW : ∀ w ∈ barW K k,
      (conjAut (2 + k) K B * fieldAut (2 + k) K τ * dualAut (2 + k) K ^ 1) w = w)
    (hL : ∀ l ∈ barL K k,
      (conjAut (2 + k) K B * fieldAut (2 + k) K τ * dualAut (2 + k) K ^ 1) l = l) : False := by
  obtain ⟨-, c, D, -, hB⟩ := fix_barW_one hW
  have hD := fix_barL_one hB hL
  have hdet := (det_ne_zero_of_blk hB).2
  set i₀ : Fin k := ⟨0, by omega⟩
  set i₁ : Fin k := ⟨1, by omega⟩
  set i₂ : Fin k := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  have h20 : i₂ ≠ i₀ := by simp [i₀, i₂, Fin.ext_iff]
  have h3 : D * single i₂ i₀ 1 = 0 :=
    calc D * single i₂ i₀ 1 = D * single i₂ i₁ 1 * single i₁ i₀ 1 := by
          rw [Matrix.mul_assoc, single_mul_single_same, mul_one]
      _ = single i₁ i₂ 1 * D * single i₁ i₀ 1 := by rw [hD i₁ i₂ h12]
      _ = single i₁ i₂ 1 * (single i₀ i₁ 1 * D) := by rw [Matrix.mul_assoc, hD i₀ i₁ h01]
      _ = 0 := by rw [← Matrix.mul_assoc, single_mul_single_of_ne (h := h20), Matrix.zero_mul]
  have h4 : single i₂ i₀ (1 : K) = 0 := by
    have h5 := congrArg (fun M => D⁻¹ * M) h3
    simp only [Matrix.mul_zero, ← Matrix.mul_assoc] at h5
    rwa [nonsing_inv_mul D (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul] at h5
  have := congrFun (congrFun h4 i₂) i₀
  simp at this

end Fix

section Torus

variable {K : Type} [Field K]

@[expose] noncomputable def torus : Kˣ →* SpecialLinearGroup (Fin (2 + 2)) K where
  toFun c := ⟨blk (((c⁻¹ : Kˣ) : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((c : K) • 1), by
    rw [det_blk, det_smul, det_smul, det_one, Fintype.card_fin, mul_one, mul_one, ← mul_pow,
      Units.inv_mul, one_pow]⟩
  map_one' := by
    apply Subtype.ext
    change blk (((1⁻¹ : Kˣ) : K) • (1 : Matrix (Fin 2) (Fin 2) K)) (((1 : Kˣ) : K) • 1) = 1
    rw [inv_one, Units.val_one, one_smul, blk_one]
  map_mul' c d := by
    apply Subtype.ext
    change blk ((((c * d)⁻¹ : Kˣ) : K) • (1 : Matrix (Fin 2) (Fin 2) K)) (((c * d : Kˣ) : K) • 1) =
      blk (((c⁻¹ : Kˣ) : K) • 1) ((c : K) • 1) * blk (((d⁻¹ : Kˣ) : K) • 1) ((d : K) • 1)
    rw [blk_mul, smul_one_mul_smul_one, smul_one_mul_smul_one, mul_inv, Units.val_mul,
      Units.val_mul]

theorem coe_torus (c : Kˣ) :
    ((torus c : SpecialLinearGroup (Fin (2 + 2)) K) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) =
      blk (((c⁻¹ : Kˣ) : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((c : K) • 1) :=
  rfl

theorem transpose_torus (c : Kˣ) : (torus c : SpecialLinearGroup (Fin (2 + 2)) K).transpose =
    torus c := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_transpose, coe_torus, transpose_blk, transpose_smul, transpose_smul,
    transpose_one]

theorem blk_mul_torus (X D : Matrix (Fin 2) (Fin 2) K) (c : Kˣ) :
    blk X D * (torus c : SpecialLinearGroup (Fin (2 + 2)) K) = (torus c : _) * blk X D := by
  rw [coe_torus, blk_mul, blk_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul]

theorem eq_one_of_torus_mem_scalars [CharP K 2] {c : Kˣ} (h : torus c ∈ scalars (2 + 2) K) :
    c = 1 := by
  obtain ⟨z, -, hz⟩ := mem_scalars.mp h
  rw [coe_torus, scalar_eq_blk] at hz
  obtain ⟨h1, h2⟩ := blk_injective hz
  have e1 := congrFun (congrFun h1 0) 0
  have e2 := congrFun (congrFun h2 0) 0
  simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at e1 e2
  have h3 : (c : K) * c = 1 * 1 :=
    calc (c : K) * c = (c : K) * ((c⁻¹ : Kˣ) : K) := by rw [e1, e2]
      _ = 1 * 1 := by rw [Units.mul_inv, one_mul]
  exact Units.ext (eq_of_mul_self_eq h3)

end Torus

section TorusFix

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] noncomputable def barT : Subgroup (projectiveSL (2 + 2) K) :=
  ((proj (2 + 2) K).comp torus).range

theorem false_of_fix_one_two {B : GL (Fin (2 + 2)) K} {τ : K ≃+* K}
    (hW : ∀ w ∈ barW K 2,
      (conjAut (2 + 2) K B * fieldAut (2 + 2) K τ * dualAut (2 + 2) K ^ 1) w = w)
    {c : Kˣ} (hc : c ≠ 1)
    (hT : (conjAut (2 + 2) K B * fieldAut (2 + 2) K τ * dualAut (2 + 2) K ^ 1)
      (proj (2 + 2) K (torus c)) = proj (2 + 2) K (torus c)) : False := by
  obtain ⟨hτ, c', D, -, hB⟩ := fix_barW_one hW
  rw [std_one_proj, ← map_inv, transpose_torus, map_eq_self hτ,
    slConjugation_eq_of_mul_eq B (h' := torus c⁻¹) (by rw [hB]; exact blk_mul_torus _ _ _)] at hT
  have h1 : torus (c⁻¹ * c⁻¹) ∈ scalars (2 + 2) K := by
    rw [← proj_eq_one_iff, map_mul, map_mul]
    nth_rewrite 2 [hT]
    rw [map_inv, map_inv, inv_mul_cancel]
  have h2 : c * c = 1 := inv_eq_one.mp (by rw [_root_.mul_inv_rev, eq_one_of_torus_mem_scalars h1])
  have h3 : (c : K) * c = 1 * 1 := by rw [← Units.val_mul, h2, Units.val_one, one_mul]
  exact hc (Units.ext (by rw [Units.val_one]; exact eq_of_mul_self_eq h3))

end TorusFix

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_one_of_fixes_of_three_le {k : ℕ} (hk : 3 ≤ k) (α : MulAut (projectiveSL (2 + k) K))
    (h2 : α * α = 1) (hW : ∀ w ∈ barW K k, α w = w) (hL : ∀ l ∈ barL K k, α l = l) : α = 1 := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 2 + k) (by omega)
  obtain ⟨B, τ, ε, hε, rfl⟩ := hgen α
  interval_cases ε
  · exact eq_one_of_fix_zero (by omega) h2 hW hL
  · exact (false_of_fix_one_of_three_le hk hW hL).elim

theorem eq_one_of_fixes_two (α : MulAut (projectiveSL (2 + 2) K)) (h2 : α * α = 1)
    (hW : ∀ w ∈ barW K 2, α w = w) (hL : ∀ l ∈ barL K 2, α l = l) {c : Kˣ} (hc : c ≠ 1)
    (hT : α (proj (2 + 2) K (torus c)) = proj (2 + 2) K (torus c)) : α = 1 := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 2 + 2) (by omega)
  obtain ⟨B, τ, ε, hε, rfl⟩ := hgen α
  interval_cases ε
  · exact eq_one_of_fix_zero (by omega) h2 hW hL
  · exact (false_of_fix_one_two hW hc hT).elim

theorem exists_inner_of_fixes_two (α : MulAut (projectiveSL (2 + 2) K))
    (hW : ∀ w ∈ barW K 2, α w = w) {c : Kˣ} (hc : c ≠ 1)
    (hT : α (proj (2 + 2) K (torus c)) = proj (2 + 2) K (torus c)) :
    ∃ l ∈ barL K 2, ∀ x ∈ barL K 2, α x = l * x * l⁻¹ := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 2 + 2) (by omega)
  obtain ⟨B, τ, ε, hε, rfl⟩ := hgen α
  interval_cases ε
  · obtain ⟨hτ, c', D, -, hB⟩ := fix_barW_zero hW
    have hdet := (det_ne_zero_of_blk hB).2
    obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' D.det
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact hdet (by rw [hμ, mul_zero])
    have hD₁ : (μ⁻¹ • D).det = 1 := by
      rw [det_smul, Fintype.card_fin, hμ, inv_pow, sq, inv_mul_cancel₀ (mul_ne_zero hμ0 hμ0)]
    set S₀ : SpecialLinearGroup (Fin 2) K := ⟨μ⁻¹ • D, hD₁⟩ with hS₀
    refine ⟨proj (2 + 2) K (blkSL₂ S₀), ⟨S₀, rfl⟩, ?_⟩
    rintro _ ⟨S, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [std_zero_proj, map_eq_self hτ, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply slConjugation_eq_of_mul_eq
    rw [← map_inv, ← map_mul, ← map_mul, coe_blkSL₂, coe_blkSL₂, hB, blk_mul, blk_mul,
      Matrix.mul_one, Matrix.one_mul]
    congr 1
    have hE : ((S₀⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * D = μ • 1 := by
      have hD : D = μ • (S₀ : Matrix (Fin 2) (Fin 2) K) := by
        rw [hS₀]
        change D = μ • μ⁻¹ • D
        rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]
      rw [hD, Matrix.mul_smul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
      hE, Matrix.mul_smul, Matrix.mul_one]
    change D * S = μ • ((μ⁻¹ • D) * S)
    rw [Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  · exact (false_of_fix_one_two hW hc hT).elim

end Main

end CFSG.ComponentClassification.RankTwoClassical
