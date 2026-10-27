module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8.L5

open Matrix
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K]

@[expose] def dot3 (b a : Fin 3 → K) : K := b 0 * a 0 + b 1 * a 1 + b 2 * a 2

theorem dot3_neg_right (b a : Fin 3 → K) : dot3 b (-a) = -dot3 b a := by
  simp only [dot3, Pi.neg_apply]; ring

theorem dot3_zero_left (a : Fin 3 → K) : dot3 0 a = 0 := by simp [dot3]

theorem dot3_zero_right (b : Fin 3 → K) : dot3 b 0 = 0 := by simp [dot3]

theorem dot3_single_right (b : Fin 3 → K) (j : Fin 3) : dot3 b (Pi.single j 1) = b j := by
  fin_cases j <;> simp [dot3]

theorem dot3_single_left (a : Fin 3 → K) (j : Fin 3) : dot3 (Pi.single j 1) a = a j := by
  fin_cases j <;> simp [dot3]

@[expose] def lomat (a b : Fin 3 → K) (z : K) : Matrix (Fin 5) (Fin 5) K :=
  !![1, 0, 0, 0, 0; a 0, 1, 0, 0, 0; a 1, 0, 1, 0, 0; a 2, 0, 0, 1, 0; z, b 0, b 1, b 2, 1]

theorem lomat_mul (a b a' b' : Fin 3 → K) (z z' : K) :
    lomat a b z * lomat a' b' z' = lomat (a + a') (b + b') (z + z' + dot3 b a') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lomat, dot3, Matrix.mul_apply, Fin.sum_univ_five] <;> ring

theorem lomat_zero : lomat (0 : Fin 3 → K) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lomat]

theorem lomat_det (a b : Fin 3 → K) (z : K) : (lomat a b z).det = 1 := by
  have h : (lomat a b z).IsLowerTriangular := by
    intro i j hij
    have hlt : i < j := hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hlt; decide) | simp [lomat]
  rw [Matrix.det_of_isLowerTriangular _ h]
  simp [lomat, Fin.prod_univ_five]

@[expose] def lo (a b : Fin 3 → K) (z : K) : SL(5, K) := ⟨lomat a b z, lomat_det a b z⟩

theorem coe_lo (a b : Fin 3 → K) (z : K) :
    ((lo a b z : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) = lomat a b z := rfl

theorem lo_mul (a b a' b' : Fin 3 → K) (z z' : K) :
    lo a b z * lo a' b' z' = lo (a + a') (b + b') (z + z' + dot3 b a') :=
  Subtype.ext (lomat_mul a b a' b' z z')

theorem lo_zero : lo (0 : Fin 3 → K) 0 0 = 1 := Subtype.ext lomat_zero

theorem lo_inv (a b : Fin 3 → K) (z : K) : (lo a b z)⁻¹ = lo (-a) (-b) (dot3 b a - z) := by
  apply inv_eq_of_mul_eq_one_right
  rw [lo_mul, ← lo_zero]
  congr 1
  · exact add_neg_cancel a
  · exact add_neg_cancel b
  · rw [dot3_neg_right]; ring

theorem lo_conj (a' b' : Fin 3 → K) (z'' : K) (a b : Fin 3 → K) (z : K) :
    lo a' b' z'' * lo a b z * (lo a' b' z'')⁻¹ = lo a b (z + dot3 b' a - dot3 b a') := by
  rw [lo_inv, lo_mul, lo_mul]
  congr 1
  · funext i; simp
  · funext i; simp
  · simp only [dot3, Pi.add_apply, Pi.neg_apply]; ring

@[expose] def LoSG (K : Type*) [Field K] : Subgroup SL(5, K) where
  carrier := {M | ∃ (a b : Fin 3 → K) (z : K), M = lo a b z}
  mul_mem' := by
    rintro _ _ ⟨a, b, z, rfl⟩ ⟨a', b', z', rfl⟩
    exact ⟨_, _, _, lo_mul a b a' b' z z'⟩
  one_mem' := ⟨0, 0, 0, lo_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, z, rfl⟩
    exact ⟨_, _, _, lo_inv a b z⟩

@[expose] def LowerPos (i j : Fin 5) : Prop := (j = 0 ∧ i ≠ 0) ∨ (i = 4 ∧ j ≠ 0 ∧ j ≠ 4)

instance (i j : Fin 5) : Decidable (LowerPos i j) :=
  inferInstanceAs (Decidable ((j = 0 ∧ i ≠ 0) ∨ (i = 4 ∧ j ≠ 0 ∧ j ≠ 4)))

@[expose] def PureDir (i j : Fin 5) : Prop :=
  (j = 0 ∧ i ≠ 0 ∧ i ≠ 4) ∨ (i = 4 ∧ j ≠ 0 ∧ j ≠ 4)

instance (i j : Fin 5) : Decidable (PureDir i j) :=
  inferInstanceAs (Decidable ((j = 0 ∧ i ≠ 0 ∧ i ≠ 4) ∨ (i = 4 ∧ j ≠ 0 ∧ j ≠ 4)))

theorem tv10 (t : K) : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 5) ≠ 0 by decide) t =
    lo ![t, 0, 0] 0 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lo, lomat, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem tv20 (t : K) : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 5) ≠ 0 by decide) t =
    lo ![0, t, 0] 0 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lo, lomat, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem tv30 (t : K) : Matrix.SpecialLinearGroup.transvection (show (3 : Fin 5) ≠ 0 by decide) t =
    lo ![0, 0, t] 0 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lo, lomat, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem tv40 (t : K) : Matrix.SpecialLinearGroup.transvection (show (4 : Fin 5) ≠ 0 by decide) t =
    lo 0 0 t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lo, lomat, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem tv41 (t : K) : Matrix.SpecialLinearGroup.transvection (show (4 : Fin 5) ≠ 1 by decide) t =
    lo 0 ![t, 0, 0] 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lo, lomat, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem tv42 (t : K) : Matrix.SpecialLinearGroup.transvection (show (4 : Fin 5) ≠ 2 by decide) t =
    lo 0 ![0, t, 0] 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lo, lomat, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem tv43 (t : K) : Matrix.SpecialLinearGroup.transvection (show (4 : Fin 5) ≠ 3 by decide) t =
    lo 0 ![0, 0, t] 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lo, lomat, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem transvection_mem_LoSG {i j : Fin 5} (hij : i ≠ j) (h : LowerPos i j) (t : K) :
    Matrix.SpecialLinearGroup.transvection hij t ∈ LoSG K := by
  fin_cases i <;> fin_cases j <;>
    first
    | (exfalso; simp [LowerPos] at h hij; done)
    | exact ⟨![t, 0, 0], 0, 0, tv10 t⟩
    | exact ⟨![0, t, 0], 0, 0, tv20 t⟩
    | exact ⟨![0, 0, t], 0, 0, tv30 t⟩
    | exact ⟨0, 0, t, tv40 t⟩
    | exact ⟨0, ![t, 0, 0], 0, tv41 t⟩
    | exact ⟨0, ![0, t, 0], 0, tv42 t⟩
    | exact ⟨0, ![0, 0, t], 0, tv43 t⟩

@[expose] def U04 (t : K) : SL(5, K) :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 5) ≠ 4 by decide) t

@[expose] def U40 (t : K) : SL(5, K) :=
  Matrix.SpecialLinearGroup.transvection (show (4 : Fin 5) ≠ 0 by decide) t

theorem coe_U04 (t : K) :
    ((U04 t : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) = 1 + Matrix.single 0 4 t := rfl

theorem coe_U40 (t : K) :
    ((U40 t : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) = 1 + Matrix.single 4 0 t := rfl

theorem U04_inv (t : K) : (U04 t)⁻¹ = U04 (-t) :=
  Matrix.SpecialLinearGroup.transvection_inv _ t

theorem row4_of_commute (X : SL(5, K)) (h : Commute X (U04 (1 : K))) :
    (X : Matrix (Fin 5) (Fin 5) K) 4 0 = 0 ∧ (X : Matrix (Fin 5) (Fin 5) K) 4 1 = 0 ∧
      (X : Matrix (Fin 5) (Fin 5) K) 4 2 = 0 ∧ (X : Matrix (Fin 5) (Fin 5) K) 4 3 = 0 := by
  have h1 : ((X * U04 (1 : K) : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
      ((U04 (1 : K) * X : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) := by rw [h.eq]
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_U04] at h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_five] using congrFun (congrFun h1 0) 0
  · simpa [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_five] using congrFun (congrFun h1 0) 1
  · simpa [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_five] using congrFun (congrFun h1 0) 2
  · simpa [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_five] using congrFun (congrFun h1 0) 3

theorem class2_fails (a b : Fin 3 → K) (z : K) (hz : z ≠ 0) :
    ¬ Commute ⁅U04 (1 : K), lo a b z⁆ (U04 (1 : K)) := by
  intro h
  obtain ⟨h0, h1, h2, h3⟩ := row4_of_commute _ h
  have e0 : ((⁅U04 (1 : K), lo a b z⁆ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) 4 0 =
      z * (z - dot3 b a) := by
    rw [commutatorElement_def, U04_inv, lo_inv]
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_U04, coe_lo, lomat, dot3, Matrix.mul_apply,
      Fin.sum_univ_five, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] <;> ring
  have e1 : ((⁅U04 (1 : K), lo a b z⁆ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) 4 1 = z * b 0 := by
    rw [commutatorElement_def, U04_inv, lo_inv]
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_U04, coe_lo, lomat, dot3, Matrix.mul_apply,
      Fin.sum_univ_five, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] <;> ring
  have e2 : ((⁅U04 (1 : K), lo a b z⁆ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) 4 2 = z * b 1 := by
    rw [commutatorElement_def, U04_inv, lo_inv]
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_U04, coe_lo, lomat, dot3, Matrix.mul_apply,
      Fin.sum_univ_five, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] <;> ring
  have e3 : ((⁅U04 (1 : K), lo a b z⁆ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) 4 3 = z * b 2 := by
    rw [commutatorElement_def, U04_inv, lo_inv]
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_U04, coe_lo, lomat, dot3, Matrix.mul_apply,
      Fin.sum_univ_five, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] <;> ring
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have hb0 : b 0 = 0 := (mul_eq_zero.1 h1).resolve_left hz
  have hb1 : b 1 = 0 := (mul_eq_zero.1 h2).resolve_left hz
  have hb2 : b 2 = 0 := (mul_eq_zero.1 h3).resolve_left hz
  have hd : dot3 b a = 0 := by simp [dot3, hb0, hb1, hb2]
  rw [hd, sub_zero] at h0
  exact hz (mul_self_eq_zero.1 h0)

@[expose] def Dich (D : Subgroup SL(5, K)) : Prop :=
  ∀ n : SL(5, K), (∀ d ∈ D, ∀ t : K, Commute ⁅U04 t, n * d * n⁻¹⁆ (U04 t)) ∨
    ∃ M : SL(5, K), ∀ g : SL(5, K), g ∈ D ↔ ∃ t : K, n * g * n⁻¹ = M * U04 t * M⁻¹

theorem exists_conj (D : Subgroup SL(5, K)) (hlo : D ≤ LoSG K) (hnt : ∃ d ∈ D, d ≠ 1)
    (hD : Dich D) :
    ∃ M : SL(5, K), ∀ g : SL(5, K), g ∈ D ↔ ∃ t : K, g = M * U04 t * M⁻¹ := by
  obtain ⟨d₀, hd₀, hne⟩ := hnt
  obtain ⟨a, b, z, rfl⟩ := hlo hd₀
  have key : ∀ (n : SL(5, K)) (z' : K), z' ≠ 0 → n * lo a b z * n⁻¹ = lo a b z' →
      ∃ M : SL(5, K), ∀ g : SL(5, K), g ∈ D ↔ ∃ t : K, g = M * U04 t * M⁻¹ := by
    intro n z' hz' hn
    rcases hD n with h1 | ⟨M, hM⟩
    · exfalso
      have h2 := h1 (lo a b z) hd₀ 1
      rw [hn] at h2
      exact class2_fails a b z' hz' h2
    · refine ⟨n⁻¹ * M, fun g => ?_⟩
      rw [hM g]
      constructor
      · rintro ⟨t, ht⟩
        refine ⟨t, ?_⟩
        calc g = n⁻¹ * (n * g * n⁻¹) * n := by group
          _ = n⁻¹ * (M * U04 t * M⁻¹) * n := by rw [ht]
          _ = n⁻¹ * M * U04 t * (n⁻¹ * M)⁻¹ := by group
      · rintro ⟨t, ht⟩
        refine ⟨t, ?_⟩
        calc n * g * n⁻¹ = n * (n⁻¹ * M * U04 t * (n⁻¹ * M)⁻¹) * n⁻¹ := by rw [ht]
          _ = M * U04 t * M⁻¹ := by group
  by_cases hz : z = 0
  · by_cases ha : a = 0
    · by_cases hb : b = 0
      · exact absurd (by rw [ha, hb, hz]; exact lo_zero) hne
      · obtain ⟨j, hj⟩ := Function.ne_iff.1 hb
        replace hj : b j ≠ 0 := hj
        refine key (lo (Pi.single j 1) 0 0) (-(b j)) (neg_ne_zero.2 hj) ?_
        rw [lo_conj, dot3_zero_left, dot3_single_right, hz]
        congr 1
        ring
    · obtain ⟨j, hj⟩ := Function.ne_iff.1 ha
      replace hj : a j ≠ 0 := hj
      refine key (lo 0 (Pi.single j 1) 0) (a j) hj ?_
      rw [lo_conj, dot3_zero_right, dot3_single_left, hz]
      congr 1
      ring
  · refine key 1 z hz ?_
    simp

@[expose] def Pm (u v : Fin 5 → K) (h : dotProduct v u = 0) : SL(5, K) :=
  ⟨1 + vecMulVec u v, by
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, h, add_zero]⟩

theorem coe_Pm (u v : Fin 5 → K) (h : dotProduct v u = 0) :
    ((Pm u v h : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) = 1 + vecMulVec u v := rfl

theorem Pm_mul_neg (u v : Fin 5 → K) (h : dotProduct v u = 0) :
    Pm u v h * Pm u (-v) (by rw [neg_dotProduct, h, neg_zero]) = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_Pm, Matrix.SpecialLinearGroup.coe_one]
  have hU : vecMulVec u (-v) = -vecMulVec u v := vecMulVec_neg u v
  have hUU : vecMulVec u v * vecMulVec u (-v) = 0 := by
    rw [vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]
  calc (1 + vecMulVec u v) * (1 + vecMulVec u (-v))
      = 1 + vecMulVec u (-v) + vecMulVec u v + vecMulVec u v * vecMulVec u (-v) := by noncomm_ring
    _ = 1 := by rw [hUU, hU]; abel

theorem Pm_inv (u v : Fin 5 → K) (h : dotProduct v u = 0) :
    (Pm u v h)⁻¹ = Pm u (-v) (by rw [neg_dotProduct, h, neg_zero]) :=
  inv_eq_of_mul_eq_one_right (Pm_mul_neg u v h)

theorem vecMulVec_comm_single04 (u v : Fin 5 → K) (hv : v 0 = 0) (hu : u 4 = 0) (t : K) :
    vecMulVec u v * Matrix.single 0 4 t = Matrix.single 0 4 t * vecMulVec u v := by
  ext p q
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.single_apply, Fin.sum_univ_five, hv, hu]

theorem vecMulVec_comm_single40 (u v : Fin 5 → K) (hv : v 4 = 0) (hu : u 0 = 0) (t : K) :
    vecMulVec u v * Matrix.single 4 0 t = Matrix.single 4 0 t * vecMulVec u v := by
  ext p q
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.single_apply, Fin.sum_univ_five, hv, hu]

theorem Pm_comm_U04 (u v : Fin 5 → K) (h : dotProduct v u = 0) (hv : v 0 = 0) (hu : u 4 = 0)
    (t : K) : Pm u v h * U04 t = U04 t * Pm u v h := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_Pm, coe_U04]
  have hc := vecMulVec_comm_single04 u v hv hu t
  calc (1 + vecMulVec u v) * (1 + Matrix.single 0 4 t)
      = 1 + vecMulVec u v + Matrix.single 0 4 t + vecMulVec u v * Matrix.single 0 4 t := by
        noncomm_ring
    _ = 1 + vecMulVec u v + Matrix.single 0 4 t + Matrix.single 0 4 t * vecMulVec u v := by
        rw [hc]
    _ = (1 + Matrix.single 0 4 t) * (1 + vecMulVec u v) := by noncomm_ring

theorem Pm_comm_U40 (u v : Fin 5 → K) (h : dotProduct v u = 0) (hv : v 4 = 0) (hu : u 0 = 0)
    (t : K) : Pm u v h * U40 t = U40 t * Pm u v h := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_Pm, coe_U40]
  have hc := vecMulVec_comm_single40 u v hv hu t
  calc (1 + vecMulVec u v) * (1 + Matrix.single 4 0 t)
      = 1 + vecMulVec u v + Matrix.single 4 0 t + vecMulVec u v * Matrix.single 4 0 t := by
        noncomm_ring
    _ = 1 + vecMulVec u v + Matrix.single 4 0 t + Matrix.single 4 0 t * vecMulVec u v := by
        rw [hc]
    _ = (1 + Matrix.single 4 0 t) * (1 + vecMulVec u v) := by noncomm_ring

theorem Pm_mulVec (u v c : Fin 5 → K) :
    (1 + vecMulVec u v) *ᵥ c = c + dotProduct v c • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext p
  first
  | (simp [Matrix.mulVec, dotProduct, vecMulVec_apply, Fin.sum_univ_five]; done)
  | (simp [Matrix.mulVec, dotProduct, vecMulVec_apply, Fin.sum_univ_five]; ring)

theorem vecMul_Pm (r u v : Fin 5 → K) :
    r ᵥ* (1 + vecMulVec u v) = r + dotProduct r u • v := by
  rw [Matrix.vecMul_add, Matrix.vecMul_one]
  congr 1
  ext q
  first
  | (simp [Matrix.vecMul, dotProduct, vecMulVec_apply, Fin.sum_univ_five]; done)
  | (simp [Matrix.vecMul, dotProduct, vecMulVec_apply, Fin.sum_univ_five]; ring)

theorem conj_rank_one (A B : Matrix (Fin 5) (Fin 5) K) (hAB : A * B = 1) (t : K)
    (c r : Fin 5 → K) :
    A * (1 + t • vecMulVec c r) * B = 1 + t • vecMulVec (A *ᵥ c) (r ᵥ* B) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAB, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

@[expose] def Pure (D : Subgroup SL(5, K)) : Prop :=
  ∃ P : SL(5, K), (∀ t : K, P * U04 t = U04 t * P) ∧ (∀ t : K, P * U40 t = U40 t * P) ∧
    ∃ (i j : Fin 5) (hij : i ≠ j), PureDir i j ∧
      ∀ d ∈ D, ∃ u v : K, P * d * P⁻¹ = Matrix.SpecialLinearGroup.transvection hij u * U40 v

theorem exists_w (c : Fin 5 → K) (hc0 : c 0 = 0) :
    ∃ (j : Fin 5) (w : Fin 5 → K), j ≠ 0 ∧ j ≠ 4 ∧ w 0 = 0 ∧ w 4 = 0 ∧ w j = 0 ∧
      ∀ p, c p + c j * w p = (if p = j then c j else 0) + (if p = 4 then c 4 else 0) := by
  by_cases hex : ∃ j : Fin 5, j ≠ 0 ∧ j ≠ 4 ∧ c j ≠ 0
  · obtain ⟨j, hj0, hj4, hcj⟩ := hex
    refine ⟨j, fun p => if p = 0 ∨ p = 4 ∨ p = j then 0 else -(c p) / c j, hj0, hj4,
      by simp, by simp, by simp, ?_⟩
    intro p
    by_cases hpj : p = j
    · rw [hpj]; simp [hj4]
    · by_cases hp4 : p = 4
      · rw [hp4]; simp [hj4, hj4.symm]
      · by_cases hp0 : p = 0
        · rw [hp0]; simp [hc0, hj0, hj0.symm, hj4, hj4.symm]
        · first
          | (simp [hpj, hp4, hp0, hcj]; done)
          | (simp [hpj, hp4, hp0]; field_simp; ring)
  · push_neg at hex
    have h1 : c 1 = 0 := hex 1 (by decide) (by decide)
    have h2 : c 2 = 0 := hex 2 (by decide) (by decide)
    have h3 : c 3 = 0 := hex 3 (by decide) (by decide)
    refine ⟨1, 0, by decide, by decide, rfl, rfl, rfl, ?_⟩
    intro p
    have hp : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 := by revert p; decide
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [hc0, h1, h2, h3]

theorem exists_rho (r : Fin 5 → K) (j : Fin 5) (hj0 : j ≠ 0) (hj4 : j ≠ 4) (hrj : r j ≠ 0)
    (hr4 : r 4 = 0) :
    ∃ ρ : Fin 5 → K, ρ 0 = 0 ∧ ρ 4 = 0 ∧ ρ j = 0 ∧
      ∀ q, r q + r j * ρ q = (if q = 0 then r 0 else 0) + (if q = j then r j else 0) := by
  refine ⟨fun q => if q = 0 ∨ q = 4 ∨ q = j then 0 else -(r q) / r j, by simp, by simp,
    by simp, ?_⟩
  intro q
  by_cases hqj : q = j
  · rw [hqj]; simp [hj0, hj0.symm]
  · by_cases hq0 : q = 0
    · rw [hq0]; simp [hj0, hj0.symm]
    · by_cases hq4 : q = 4
      · rw [hq4]; simp [hr4, hj4, hj4.symm]
      · first
        | (simp [hqj, hq0, hq4, hrj]; done)
        | (simp [hqj, hq0, hq4]; field_simp; ring)

theorem single_prod_zero (j : Fin 5) (u v : K) :
    (Matrix.single j 0 u : Matrix (Fin 5) (Fin 5) K) * Matrix.single 4 0 v = 0 := by
  ext p q
  simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_five]

theorem single_prod_zero' (j : Fin 5) (hj : j ≠ 4) (u v : K) :
    (Matrix.single 4 j u : Matrix (Fin 5) (Fin 5) K) * Matrix.single 4 0 v = 0 := by
  ext p q
  simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_five, hj, hj.symm]

theorem pure_typeA (D : Subgroup SL(5, K)) (M : SL(5, K)) (c r : Fin 5 → K) (r₀ : K)
    (hDM : ∀ g : SL(5, K), g ∈ D ↔ ∃ t : K, g = M * U04 t * M⁻¹)
    (hconj : ∀ t : K, ((M * U04 t * M⁻¹ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
      1 + t • vecMulVec c r)
    (hc0 : c 0 = 0) (hr : ∀ q, r q = if q = 0 then r₀ else 0) : Pure D := by
  obtain ⟨j, w, hj0, hj4, hw0, hw4, hwj, hPc⟩ := exists_w c hc0
  have hh : dotProduct (Pi.single j (1 : K)) w = 0 := by simp [hwj]
  refine ⟨Pm w (Pi.single j 1) hh, ?_, ?_, j, 0, hj0, Or.inl ⟨rfl, hj0, hj4⟩, ?_⟩
  · intro t
    exact Pm_comm_U04 _ _ hh (by simp [Pi.single_apply, hj0.symm]) hw4 t
  · intro t
    exact Pm_comm_U40 _ _ hh (by simp [Pi.single_apply, hj4.symm]) hw0 t
  · intro d hd
    obtain ⟨t, rfl⟩ := (hDM d).1 hd
    refine ⟨t * c j * r₀, t * c 4 * r₀, ?_⟩
    have hB : ((Pm w (Pi.single j 1) hh)⁻¹ : SL(5, K)) = Pm w (-(Pi.single j 1))
        (by rw [neg_dotProduct, hh, neg_zero]) := Pm_inv _ _ hh
    have hAB : ((Pm w (Pi.single j 1) hh : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) *
        (((Pm w (Pi.single j 1) hh)⁻¹ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
    have hAc : ((Pm w (Pi.single j 1) hh : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) *ᵥ c =
        fun p => c p + c j * w p := by
      rw [coe_Pm, Pm_mulVec]
      ext p
      simp
    have hrB : r ᵥ* (((Pm w (Pi.single j 1) hh)⁻¹ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) = r := by
      rw [hB, coe_Pm, vecMul_Pm]
      have : dotProduct r w = 0 := by
        simp [dotProduct, hr, Fin.sum_univ_five, hw0]
      simp [this]
    have key : ((Pm w (Pi.single j 1) hh * (M * U04 t * M⁻¹) * (Pm w (Pi.single j 1) hh)⁻¹ :
        SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
        1 + t • vecMulVec (fun p => c p + c j * w p) r := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hconj t,
        conj_rank_one _ _ hAB, hAc, hrB]
    apply Subtype.ext
    rw [key]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      coe_U40]
    have hprod := single_prod_zero (K := K) j (t * c j * r₀) (t * c 4 * r₀)
    calc (1 : Matrix (Fin 5) (Fin 5) K) + t • vecMulVec (fun p => c p + c j * w p) r
        = 1 + Matrix.single j 0 (t * c j * r₀) + Matrix.single 4 0 (t * c 4 * r₀) := by
          ext p q
          simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
            Matrix.single_apply, hPc p, hr q]
          rcases eq_or_ne p j with hp | hpj
          · subst hp
            rcases eq_or_ne q 0 with hq | hq
            · subst hq
              first
              | (simp [hj4, hj4.symm]; done)
              | (simp [hj4, hj4.symm]; ring)
            · simp [hq, hq.symm, hj4, hj4.symm]
          · rcases eq_or_ne p 4 with hp4 | hp4
            · subst hp4
              rcases eq_or_ne q 0 with hq | hq
              · subst hq
                first
                | (simp [hpj, hpj.symm]; done)
                | (simp [hpj, hpj.symm]; ring)
              · simp [hq, hq.symm, hpj, hpj.symm]
            · simp [hpj, hpj.symm, hp4, hp4.symm]
      _ = (1 + Matrix.single j 0 (t * c j * r₀)) * (1 + Matrix.single 4 0 (t * c 4 * r₀)) := by
          calc (1 : Matrix (Fin 5) (Fin 5) K) + Matrix.single j 0 (t * c j * r₀) +
                Matrix.single 4 0 (t * c 4 * r₀)
              = 1 + Matrix.single j 0 (t * c j * r₀) + Matrix.single 4 0 (t * c 4 * r₀) +
                  Matrix.single j 0 (t * c j * r₀) * Matrix.single 4 0 (t * c 4 * r₀) := by
                rw [hprod, add_zero]
            _ = _ := by noncomm_ring

theorem pure_typeB (D : Subgroup SL(5, K)) (M : SL(5, K)) (c r : Fin 5 → K) (j : Fin 5)
    (hj0 : j ≠ 0) (hj4 : j ≠ 4) (hrj : r j ≠ 0) (hr4 : r 4 = 0)
    (hcz : ∀ p, p ≠ 4 → c p = 0)
    (hDM : ∀ g : SL(5, K), g ∈ D ↔ ∃ t : K, g = M * U04 t * M⁻¹)
    (hconj : ∀ t : K, ((M * U04 t * M⁻¹ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
      1 + t • vecMulVec c r) : Pure D := by
  have hc : ∀ p, c p = if p = 4 then c 4 else 0 := by
    intro p
    by_cases hp : p = 4
    · rw [hp]; simp
    · simp [hp, hcz p hp]
  obtain ⟨ρ, hρ0, hρ4, hρj, hρ⟩ := exists_rho r j hj0 hj4 hrj hr4
  have hh : dotProduct (-ρ) (Pi.single j (1 : K)) = 0 := by simp [hρj]
  refine ⟨Pm (Pi.single j 1) (-ρ) hh, ?_, ?_, 4, j, hj4.symm, Or.inr ⟨rfl, hj0, hj4⟩, ?_⟩
  · intro t
    exact Pm_comm_U04 _ _ hh (by simp [hρ0]) (by simp [Pi.single_apply, hj4.symm]) t
  · intro t
    exact Pm_comm_U40 _ _ hh (by simp [hρ4]) (by simp [Pi.single_apply, hj0.symm]) t
  · intro d hd
    obtain ⟨t, rfl⟩ := (hDM d).1 hd
    refine ⟨t * c 4 * r j, t * c 4 * r 0, ?_⟩
    have hB : ((Pm (Pi.single j 1) (-ρ) hh)⁻¹ : SL(5, K)) = Pm (Pi.single j 1) (-(-ρ))
        (by rw [neg_dotProduct, hh, neg_zero]) := Pm_inv _ _ hh
    have hAB : ((Pm (Pi.single j 1) (-ρ) hh : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) *
        (((Pm (Pi.single j 1) (-ρ) hh)⁻¹ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
    have hAc : ((Pm (Pi.single j 1) (-ρ) hh : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) *ᵥ c = c := by
      rw [coe_Pm, Pm_mulVec]
      have : dotProduct (-ρ) c = 0 := by
        simp [dotProduct, Fin.sum_univ_five, hcz 0 (by decide), hcz 1 (by decide),
          hcz 2 (by decide), hcz 3 (by decide), hρ4]
      simp [this]
    have hrB : r ᵥ* (((Pm (Pi.single j 1) (-ρ) hh)⁻¹ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
        fun q => r q + r j * ρ q := by
      rw [hB, coe_Pm, vecMul_Pm]
      ext q
      simp
    have key : ((Pm (Pi.single j 1) (-ρ) hh * (M * U04 t * M⁻¹) * (Pm (Pi.single j 1) (-ρ) hh)⁻¹ :
        SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
        1 + t • vecMulVec c (fun q => r q + r j * ρ q) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hconj t,
        conj_rank_one _ _ hAB, hAc, hrB]
    apply Subtype.ext
    rw [key]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      coe_U40]
    have hprod := single_prod_zero' (K := K) j hj4 (t * c 4 * r j) (t * c 4 * r 0)
    calc (1 : Matrix (Fin 5) (Fin 5) K) + t • vecMulVec c (fun q => r q + r j * ρ q)
        = 1 + Matrix.single 4 j (t * c 4 * r j) + Matrix.single 4 0 (t * c 4 * r 0) := by
          ext p q
          simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
            Matrix.single_apply, hρ q, hc p]
          rcases eq_or_ne p 4 with hp | hp
          · subst hp
            rcases eq_or_ne q 0 with hq | hq
            · subst hq
              first
              | (simp [hj0, hj0.symm]; done)
              | (simp [hj0, hj0.symm]; ring)
            · rcases eq_or_ne q j with hqj | hqj
              · subst hqj
                first
                | (simp [hq, hq.symm, hj0, hj0.symm]; done)
                | (simp [hq, hq.symm, hj0, hj0.symm]; ring)
              · simp [hq, hq.symm, hqj, hqj.symm]
          · simp [hp, hp.symm]
      _ = (1 + Matrix.single 4 j (t * c 4 * r j)) * (1 + Matrix.single 4 0 (t * c 4 * r 0)) := by
          calc (1 : Matrix (Fin 5) (Fin 5) K) + Matrix.single 4 j (t * c 4 * r j) +
                Matrix.single 4 0 (t * c 4 * r 0)
              = 1 + Matrix.single 4 j (t * c 4 * r j) + Matrix.single 4 0 (t * c 4 * r 0) +
                  Matrix.single 4 j (t * c 4 * r j) * Matrix.single 4 0 (t * c 4 * r 0) := by
                rw [hprod, add_zero]
            _ = _ := by noncomm_ring

theorem pure_of_dich (D : Subgroup SL(5, K)) (hlo : D ≤ LoSG K) (hnt : ∃ d ∈ D, d ≠ 1)
    (hD : Dich D) : Pure D := by
  obtain ⟨M, hDM⟩ := exists_conj D hlo hnt hD
  obtain ⟨c, hc⟩ : ∃ c : Fin 5 → K, ∀ p, c p = (M : Matrix (Fin 5) (Fin 5) K) p 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Fin 5 → K, ∀ q,
      r q = ((M⁻¹ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) 4 q := ⟨_, fun _ => rfl⟩
  have hconj : ∀ t : K, ((M * U04 t * M⁻¹ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
      1 + t • vecMulVec c r := by
    intro t
    have h1 : (M : Matrix (Fin 5) (Fin 5) K) * ((M⁻¹ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
        1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_U04]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
    congr 1
    ext p q
    simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_five, vecMulVec_apply, hc, hr]
    ring
  have hmem1 : M * U04 1 * M⁻¹ ∈ D := (hDM _).2 ⟨1, rfl⟩
  obtain ⟨a, b, z, habz⟩ := hlo hmem1
  have hent : ∀ p q, (1 : Matrix (Fin 5) (Fin 5) K) p q + c p * r q = lomat a b z p q := by
    intro p q
    have h' := hconj 1
    rw [habz, coe_lo] at h'
    have := (congrFun (congrFun h' p) q).symm
    simpa [vecMulVec_apply] using this
  have e00 : c 0 * r 0 = 0 := by simpa [lomat] using hent 0 0
  have e01 : c 0 * r 1 = 0 := by simpa [lomat] using hent 0 1
  have e02 : c 0 * r 2 = 0 := by simpa [lomat] using hent 0 2
  have e03 : c 0 * r 3 = 0 := by simpa [lomat] using hent 0 3
  have e04 : c 0 * r 4 = 0 := by simpa [lomat] using hent 0 4
  have e11 : c 1 * r 1 = 0 := by simpa [lomat] using hent 1 1
  have e12 : c 1 * r 2 = 0 := by simpa [lomat] using hent 1 2
  have e13 : c 1 * r 3 = 0 := by simpa [lomat] using hent 1 3
  have e14 : c 1 * r 4 = 0 := by simpa [lomat] using hent 1 4
  have e21 : c 2 * r 1 = 0 := by simpa [lomat] using hent 2 1
  have e22 : c 2 * r 2 = 0 := by simpa [lomat] using hent 2 2
  have e23 : c 2 * r 3 = 0 := by simpa [lomat] using hent 2 3
  have e24 : c 2 * r 4 = 0 := by simpa [lomat] using hent 2 4
  have e31 : c 3 * r 1 = 0 := by simpa [lomat] using hent 3 1
  have e32 : c 3 * r 2 = 0 := by simpa [lomat] using hent 3 2
  have e33 : c 3 * r 3 = 0 := by simpa [lomat] using hent 3 3
  have e34 : c 3 * r 4 = 0 := by simpa [lomat] using hent 3 4
  have e44 : c 4 * r 4 = 0 := by simpa [lomat] using hent 4 4
  have hcne : ∃ p, c p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : ∀ p, (M : Matrix (Fin 5) (Fin 5) K) p 0 = 0 := fun p => by rw [← hc]; exact hcon p
    have h1 : ((M⁻¹ * M : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) 0 0 = 1 := by simp
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply] at h1
    simp [hz] at h1
  have hrne : ∃ q, r q ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : ∀ q, ((M⁻¹ : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) 4 q = 0 :=
      fun q => by rw [← hr]; exact hcon q
    have h1 : ((M⁻¹ * M : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) 4 4 = 1 := by simp
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply] at h1
    simp [hz] at h1
  have hfin : ∀ q : Fin 5, q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by decide
  by_cases hB : r 1 ≠ 0 ∨ r 2 ≠ 0 ∨ r 3 ≠ 0
  ·
    have hcz : ∀ p : Fin 5, p ≠ 4 → c p = 0 := by
      intro p hp
      have hp' : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by revert p; decide
      rcases hB with h1 | h2 | h3
      · rcases hp' with rfl | rfl | rfl | rfl
        · exact (mul_eq_zero.1 e01).resolve_right h1
        · exact (mul_eq_zero.1 e11).resolve_right h1
        · exact (mul_eq_zero.1 e21).resolve_right h1
        · exact (mul_eq_zero.1 e31).resolve_right h1
      · rcases hp' with rfl | rfl | rfl | rfl
        · exact (mul_eq_zero.1 e02).resolve_right h2
        · exact (mul_eq_zero.1 e12).resolve_right h2
        · exact (mul_eq_zero.1 e22).resolve_right h2
        · exact (mul_eq_zero.1 e32).resolve_right h2
      · rcases hp' with rfl | rfl | rfl | rfl
        · exact (mul_eq_zero.1 e03).resolve_right h3
        · exact (mul_eq_zero.1 e13).resolve_right h3
        · exact (mul_eq_zero.1 e23).resolve_right h3
        · exact (mul_eq_zero.1 e33).resolve_right h3
    have hc4 : c 4 ≠ 0 := by
      obtain ⟨p, hp⟩ := hcne
      have : p = 4 := by
        by_contra h
        exact hp (hcz p h)
      rwa [this] at hp
    have hr4 : r 4 = 0 := (mul_eq_zero.1 e44).resolve_left hc4
    obtain ⟨j, hj0, hj4, hrj⟩ : ∃ j : Fin 5, j ≠ 0 ∧ j ≠ 4 ∧ r j ≠ 0 := by
      rcases hB with h | h | h
      · exact ⟨1, by decide, by decide, h⟩
      · exact ⟨2, by decide, by decide, h⟩
      · exact ⟨3, by decide, by decide, h⟩
    exact pure_typeB D M c r j hj0 hj4 hrj hr4 hcz hDM hconj
  ·
    push_neg at hB
    obtain ⟨hr1, hr2, hr3⟩ := hB
    have hr4 : r 4 = 0 := by
      by_contra h4
      obtain ⟨p, hp⟩ := hcne
      apply hp
      rcases hfin p with rfl | rfl | rfl | rfl | rfl
      · exact (mul_eq_zero.1 e04).resolve_right h4
      · exact (mul_eq_zero.1 e14).resolve_right h4
      · exact (mul_eq_zero.1 e24).resolve_right h4
      · exact (mul_eq_zero.1 e34).resolve_right h4
      · exact (mul_eq_zero.1 e44).resolve_right h4
    have hr0 : r 0 ≠ 0 := by
      obtain ⟨q, hq⟩ := hrne
      rcases hfin q with rfl | rfl | rfl | rfl | rfl
      · exact hq
      · exact absurd hr1 hq
      · exact absurd hr2 hq
      · exact absurd hr3 hq
      · exact absurd hr4 hq
    have hc0 : c 0 = 0 := (mul_eq_zero.1 e00).resolve_right hr0
    have hr' : ∀ q, r q = if q = 0 then r 0 else 0 := by
      intro q
      rcases hfin q with rfl | rfl | rfl | rfl | rfl <;> simp [hr1, hr2, hr3, hr4]
    exact pure_typeA D M c r (r 0) hDM hconj hc0 hr'

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8.L5
