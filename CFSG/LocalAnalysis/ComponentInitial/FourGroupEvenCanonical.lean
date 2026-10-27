module

public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

namespace FourGroupEvenCanonical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : Type*} [Field k]

@[expose] def matrixIsometryGroup (C : Matrix ι ι k) : Subgroup (GL ι k) where
  carrier := {g | (g : Matrix ι ι k)ᵀ * C * g = C}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq, Units.val_mul, transpose_mul] at hg hh ⊢
    rw [show (h : Matrix ι ι k)ᵀ * (g : Matrix ι ι k)ᵀ * C * (g * h) =
      (h : Matrix ι ι k)ᵀ * ((g : Matrix ι ι k)ᵀ * C * g) * h by simp only [Matrix.mul_assoc],
      hg, hh]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    set a : Matrix ι ι k := (g : Matrix ι ι k)
    set b : Matrix ι ι k := ((g⁻¹ : GL ι k) : Matrix ι ι k)
    have h2 : a * b = 1 := by
      simp only [a, b]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc bᵀ * C * b = bᵀ * (aᵀ * C * a) * b := by rw [hg]
      _ = (a * b)ᵀ * C * (a * b) := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = C := by rw [h2, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_matrixIsometryGroup {C : Matrix ι ι k} {g : GL ι k} :
    g ∈ matrixIsometryGroup C ↔ (g : Matrix ι ι k)ᵀ * C * g = C :=
  Iff.rfl

variable [CharP k 2]

theorem det_eq_one_of_mem {C : Matrix ι ι k} (hC : C.det ≠ 0) {g : GL ι k}
    (hg : g ∈ matrixIsometryGroup C) : (g : Matrix ι ι k).det = 1 := by
  have h := congrArg Matrix.det hg
  rw [det_mul, det_mul, det_transpose] at h
  have h1 : (g : Matrix ι ι k).det * (g : Matrix ι ι k).det = 1 := by
    have h' : ((g : Matrix ι ι k).det * (g : Matrix ι ι k).det - 1) * C.det = 0 := by
      linear_combination h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hC)
  have h2 : ((g : Matrix ι ι k).det - 1) ^ 2 = 0 := by
    linear_combination h1 + (1 - (g : Matrix ι ι k).det) * CharTwo.two_eq_zero (R := k)
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.mp h2)

theorem eq_one_of_mem_of_scalar {C : Matrix ι ι k} (hC : C ≠ 0) {g : GL ι k}
    (hg : g ∈ matrixIsometryGroup C) {c : k} (hc : (g : Matrix ι ι k) = scalar ι c) : g = 1 := by
  rw [mem_matrixIsometryGroup, hc, scalar_apply, ← smul_one_eq_diagonal] at hg
  simp only [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_smul] at hg
  have hc2 : c * c = 1 := by
    by_contra hne
    apply hC
    have h0 : (c * c - 1) • C = 0 := by rw [sub_smul, hg, one_smul, sub_self]
    exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)
  have hc1 : c = 1 := by
    have h2 : (c - 1) ^ 2 = 0 := by
      linear_combination hc2 + (1 - c) * CharTwo.two_eq_zero (R := k)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.mp h2)
  refine Units.ext ?_
  rw [hc, hc1, scalar_apply, Units.val_one, ← smul_one_eq_diagonal, one_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem matrix_add_self (M : Matrix ι ι k) : M + M = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (M i j)

@[expose] def nilMatrix (C : Matrix ι ι k) (c : k) (u : ι → k) : Matrix ι ι k :=
  c • vecMulVec (C *ᵥ u) u

omit [CharP k 2] in
theorem nilMatrix_mul_nilMatrix (C : Matrix ι ι k) (c d : k) (u v : ι → k) :
    nilMatrix C c u * nilMatrix C d v = (c * d * (u ⬝ᵥ (C *ᵥ v))) • vecMulVec (C *ᵥ u) v := by
  rw [nilMatrix, nilMatrix, smul_mul_smul_comm, vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [CharP k 2] in
theorem nilMatrix_mul_nilMatrix_eq_zero (C : Matrix ι ι k) (c d : k) {u v : ι → k}
    (huv : u ⬝ᵥ (C *ᵥ v) = 0) : nilMatrix C c u * nilMatrix C d v = 0 := by
  rw [nilMatrix_mul_nilMatrix, huv, mul_zero, zero_smul]

theorem one_add_mul_self {N : Matrix ι ι k} (hN : N * N = 0) : (1 + N) * (1 + N) = 1 := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, hN, add_zero, add_assoc, matrix_add_self, add_zero]

@[expose] def unipotentGL (N : Matrix ι ι k) (hN : N * N = 0) : GL ι k :=
  ⟨1 + N, 1 + N, one_add_mul_self hN, one_add_mul_self hN⟩

theorem coe_unipotentGL (N : Matrix ι ι k) (hN : N * N = 0) :
    (unipotentGL N hN : Matrix ι ι k) = 1 + N :=
  rfl

theorem unipotentGL_mem {C : Matrix ι ι k} (hCt : Cᵀ = C) (hC2 : C * C = 1) {u : ι → k}
    (hu : u ⬝ᵥ (C *ᵥ u) = 0) (c : k) :
    unipotentGL (nilMatrix C c u) (nilMatrix_mul_nilMatrix_eq_zero C c c hu) ∈
      matrixIsometryGroup C := by
  rw [mem_matrixIsometryGroup, coe_unipotentGL, nilMatrix]
  have hCCu : C *ᵥ (C *ᵥ u) = u := by rw [mulVec_mulVec, hC2, one_mulVec]
  have hCN : C * (c • vecMulVec (C *ᵥ u) u) = c • vecMulVec u u := by
    rw [Matrix.mul_smul, mul_vecMulVec, hCCu]
  have hvm : (C *ᵥ u) ᵥ* C = u := by
    rw [show (C *ᵥ u) ᵥ* C = (C *ᵥ u) ᵥ* Cᵀ by rw [hCt], vecMul_transpose, hCCu]
  have hNC : (c • vecMulVec (C *ᵥ u) u)ᵀ * C = c • vecMulVec u u := by
    rw [transpose_smul, transpose_vecMulVec, Matrix.smul_mul, vecMulVec_mul, hvm]
  have hNCN : c • vecMulVec u u * (c • vecMulVec (C *ᵥ u) u) = 0 := by
    rw [smul_mul_smul_comm, vecMulVec_mul_vecMulVec, hu, zero_smul]
    simp
  rw [transpose_add, transpose_one, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
    Matrix.mul_add, Matrix.mul_one, Matrix.mul_one, hCN, hNC, hNCN, add_zero, add_assoc,
    matrix_add_self, add_zero]

theorem exists_four_of_nil {C : Matrix ι ι k} {N₁ N₂ : Matrix ι ι k} (h₁ : N₁ * N₁ = 0)
    (h₂ : N₂ * N₂ = 0) (h₁₂ : N₁ * N₂ = N₂ * N₁) (hN₁ : N₁ ≠ 0) (hN₂ : N₂ ≠ 0) (hne : N₁ ≠ N₂)
    (hm₁ : unipotentGL N₁ h₁ ∈ matrixIsometryGroup C)
    (hm₂ : unipotentGL N₂ h₂ ∈ matrixIsometryGroup C) :
    ∃ V : Subgroup (GL ι k), V ≤ matrixIsometryGroup C ∧ CFSG.IsElementaryAbelian 2 V ∧
      Nat.card V = 4 := by
  have hx : unipotentGL N₁ h₁ * unipotentGL N₁ h₁ = 1 := Units.ext (one_add_mul_self h₁)
  have hy : unipotentGL N₂ h₂ * unipotentGL N₂ h₂ = 1 := Units.ext (one_add_mul_self h₂)
  have hxy : unipotentGL N₁ h₁ * unipotentGL N₂ h₂ = unipotentGL N₂ h₂ * unipotentGL N₁ h₁ := by
    refine Units.ext ?_
    simp only [Units.val_mul, coe_unipotentGL, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, h₁₂]
    abel
  have hx1 : unipotentGL N₁ h₁ ≠ 1 := fun h => hN₁ (by
    have := congrArg Units.val h
    rw [coe_unipotentGL, Units.val_one] at this
    simpa using this)
  have hy1 : unipotentGL N₂ h₂ ≠ 1 := fun h => hN₂ (by
    have := congrArg Units.val h
    rw [coe_unipotentGL, Units.val_one] at this
    simpa using this)
  have hxne : unipotentGL N₁ h₁ ≠ unipotentGL N₂ h₂ := fun h => hne (by
    have := congrArg Units.val h
    rw [coe_unipotentGL, coe_unipotentGL] at this
    simpa using this)
  obtain ⟨V, -, hVle, hV, hVcard⟩ := FourGroup.exists_kleinFour hx hy hxy hx1 hy1 hxne
  exact ⟨V, hVle _ hm₁ hm₂, hV, hVcard⟩

theorem det_and_scalar [Nonempty ι] {C : Matrix ι ι k} (hC2 : C * C = 1) :
    (∀ g ∈ matrixIsometryGroup C, (g : Matrix ι ι k).det = 1) ∧
      ∀ g ∈ matrixIsometryGroup C, ∀ c : k, (g : Matrix ι ι k) = scalar ι c → g = 1 := by
  have hdet : C.det ≠ 0 := fun h => by
    have := congrArg Matrix.det hC2
    rw [det_mul, h, zero_mul, det_one] at this
    exact zero_ne_one this
  have hC0 : C ≠ 0 := fun h => by
    rw [h, Matrix.zero_mul] at hC2
    exact zero_ne_one hC2
  exact ⟨fun g hg => det_eq_one_of_mem hdet hg, fun g hg c hc => eq_one_of_mem_of_scalar hC0 hg hc⟩

end FourGroupEvenCanonical

open FourGroupEvenCanonical

theorem even_canonical_identity_isometry_four_group {k : Type*} [Field k] [Finite k] [CharP k 2]
    {n : ℕ} (hn : 3 ≤ n) (hnk : (n, Nat.card k) ≠ (3, 2)) :
    (∃ V : Subgroup (GL (Fin n) k), V ≤ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k) ∧
        CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4) ∧
      (∀ g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k),
        (g : Matrix (Fin n) (Fin n) k).det = 1) ∧
      ∀ g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k), ∀ c : k,
        (g : Matrix (Fin n) (Fin n) k) = scalar (Fin n) c → g = 1 := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨?_, det_and_scalar (by rw [Matrix.one_mul])⟩
  have hCt : (1 : Matrix (Fin n) (Fin n) k)ᵀ = 1 := transpose_one
  have hC2 : (1 : Matrix (Fin n) (Fin n) k) * 1 = 1 := Matrix.one_mul 1
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let u : Fin n → k := Pi.single i0 1 + Pi.single i1 1
  have hu : u ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) k) *ᵥ u) = 0 := by
    simp [one_mulVec, u, dotProduct_add, h01, h01.symm, CharTwo.add_self_eq_zero]
  have hN0 : ∀ c : k, nilMatrix (1 : Matrix (Fin n) (Fin n) k) c u i0 i0 = c := fun c => by
    simp [nilMatrix, u, vecMulVec_apply, h01.symm]
  by_cases hn4 : 4 ≤ n
  ·
    let i2 : Fin n := ⟨2, by omega⟩
    let i3 : Fin n := ⟨3, by omega⟩
    have h23 : i2 ≠ i3 := by simp [i2, i3, Fin.ext_iff]
    have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    have h03 : i0 ≠ i3 := by simp [i0, i3, Fin.ext_iff]
    have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
    have h13 : i1 ≠ i3 := by simp [i1, i3, Fin.ext_iff]
    let v : Fin n → k := Pi.single i2 1 + Pi.single i3 1
    have hv : v ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) k) *ᵥ v) = 0 := by
      simp [one_mulVec, v, dotProduct_add, h23, h23.symm, CharTwo.add_self_eq_zero]
    have huv : u ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) k) *ᵥ v) = 0 := by
      simp [u, v, dotProduct_add, h02, h03, h12, h13]
    have hvu : v ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) k) *ᵥ u) = 0 := by
      simp [u, v, dotProduct_add, h02.symm, h03.symm, h12.symm, h13.symm]
    refine exists_four_of_nil (N₁ := nilMatrix 1 1 u) (N₂ := nilMatrix 1 1 v)
      (nilMatrix_mul_nilMatrix_eq_zero _ _ _ hu) (nilMatrix_mul_nilMatrix_eq_zero _ _ _ hv)
      (by rw [nilMatrix_mul_nilMatrix_eq_zero _ _ _ huv, nilMatrix_mul_nilMatrix_eq_zero _ _ _ hvu])
      (fun h => by simpa [hN0] using congrFun (congrFun h i0) i0) ?_ ?_
      (unipotentGL_mem hCt hC2 hu 1) (unipotentGL_mem hCt hC2 hv 1)
    · intro h
      have := congrFun (congrFun h i2) i2
      simp [nilMatrix, v, vecMulVec_apply, h23.symm] at this
    · intro h
      have := congrFun (congrFun h i0) i0
      rw [hN0] at this
      simp [nilMatrix, v, vecMulVec_apply, h02, h03] at this
  ·
    have hn3 : n = 3 := by omega
    have hk2 : Nat.card k ≠ 2 := fun h => hnk (by rw [hn3, h])
    have := Fintype.ofFinite k
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({0, 1} : Finset k))
      (t := Finset.univ) (by
        rw [Finset.card_univ, Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card]
        have h2 : 2 ≤ Nat.card k := Finite.one_lt_card
        omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    refine exists_four_of_nil (N₁ := nilMatrix 1 1 u) (N₂ := nilMatrix 1 a u)
      (nilMatrix_mul_nilMatrix_eq_zero _ _ _ hu) (nilMatrix_mul_nilMatrix_eq_zero _ _ _ hu)
      (by rw [nilMatrix_mul_nilMatrix_eq_zero _ _ _ hu, nilMatrix_mul_nilMatrix_eq_zero _ _ _ hu])
      (fun h => by simpa [hN0] using congrFun (congrFun h i0) i0)
      (fun h => ha.1 (by simpa [hN0] using congrFun (congrFun h i0) i0))
      (fun h => ha.2 (by simpa [hN0] using (congrFun (congrFun h i0) i0).symm))
      (unipotentGL_mem hCt hC2 hu 1) (unipotentGL_mem hCt hC2 hu a)

theorem even_canonical_paired_isometry_four_group {k : Type*} [Field k] [CharP k 2] {r : ℕ}
    (hr : 3 ≤ r + r) :
    (∃ V : Subgroup (GL (Fin r ⊕ Fin r) k),
        V ≤ matrixIsometryGroup (fromBlocks 0 1 1 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) ∧
        CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4) ∧
      (∀ g ∈ matrixIsometryGroup (fromBlocks 0 1 1 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k),
        (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).det = 1) ∧
      ∀ g ∈ matrixIsometryGroup (fromBlocks 0 1 1 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k),
        ∀ c : k, (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = scalar (Fin r ⊕ Fin r) c →
          g = 1 := by
  classical
  set J : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k := fromBlocks 0 1 1 0 with hJ
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hCt : Jᵀ = J := by rw [hJ, fromBlocks_transpose]; simp
  have hC2 : J * J = 1 := by rw [hJ, fromBlocks_multiply]; simp [fromBlocks_one]
  refine ⟨?_, det_and_scalar hC2⟩
  let i0 : Fin r := ⟨0, by omega⟩
  let i1 : Fin r := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let u : Fin r ⊕ Fin r → k := Pi.single (Sum.inr i0) 1
  let v : Fin r ⊕ Fin r → k := Pi.single (Sum.inr i1) 1
  have hJu : ∀ (j : Fin r) (a : Fin r ⊕ Fin r),
      (J *ᵥ Pi.single (Sum.inr j) (1 : k)) a = J a (Sum.inr j) := fun j a => by
    simp [mulVec_single]
  have hdot : ∀ i j : Fin r, Pi.single (Sum.inr i) (1 : k) ⬝ᵥ (J *ᵥ Pi.single (Sum.inr j) 1) =
      0 := fun i j => by
    rw [single_dotProduct, one_mul, hJu, hJ, fromBlocks_apply₂₂, Matrix.zero_apply]
  have hN : ∀ (c : k) (j : Fin r), nilMatrix J c (Pi.single (Sum.inr j) 1) (Sum.inl i0)
      (Sum.inr i0) = if j = i0 then c else 0 := fun c j => by
    rw [nilMatrix, Matrix.smul_apply, vecMulVec_apply, hJu, hJ, fromBlocks_apply₁₂, one_apply,
      Pi.single_apply]
    by_cases hj : j = i0
    · subst hj
      simp
    · simp [hj, Ne.symm hj]
  refine exists_four_of_nil (N₁ := nilMatrix J 1 u) (N₂ := nilMatrix J 1 v)
    (nilMatrix_mul_nilMatrix_eq_zero _ _ _ (hdot i0 i0))
    (nilMatrix_mul_nilMatrix_eq_zero _ _ _ (hdot i1 i1))
    (by rw [nilMatrix_mul_nilMatrix_eq_zero _ _ _ (hdot i0 i1),
      nilMatrix_mul_nilMatrix_eq_zero _ _ _ (hdot i1 i0)])
    (fun h => by simpa [u, hN] using congrFun (congrFun h (Sum.inl i0)) (Sum.inr i0)) ?_ ?_
    (unipotentGL_mem hCt hC2 (hdot i0 i0) 1) (unipotentGL_mem hCt hC2 (hdot i1 i1) 1)
  · intro h
    have := congrFun (congrFun h (Sum.inl i1)) (Sum.inr i1)
    simp [nilMatrix, v, vecMulVec_apply, hJ] at this
  · intro h
    have := congrFun (congrFun h (Sum.inl i0)) (Sum.inr i0)
    simp only [u, v, hN, h01.symm, ite_true, ite_false] at this
    exact one_ne_zero this

theorem even_canonical_symmetric_isometry_four_group {k : Type*} [Field k] [Finite k]
    [CharP k 2] :
    (∀ n : ℕ, 3 ≤ n → (n, Nat.card k) ≠ (3, 2) →
      (∃ V : Subgroup (GL (Fin n) k), V ≤ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k) ∧
          CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4) ∧
        (∀ g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k),
          (g : Matrix (Fin n) (Fin n) k).det = 1) ∧
        ∀ g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k), ∀ c : k,
          (g : Matrix (Fin n) (Fin n) k) = scalar (Fin n) c → g = 1) ∧
    ∀ r : ℕ, 3 ≤ r + r →
      (∃ V : Subgroup (GL (Fin r ⊕ Fin r) k),
          V ≤ matrixIsometryGroup (fromBlocks 0 1 1 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) ∧
          CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4) ∧
        (∀ g ∈ matrixIsometryGroup
            (fromBlocks 0 1 1 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k),
          (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).det = 1) ∧
        ∀ g ∈ matrixIsometryGroup (fromBlocks 0 1 1 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k),
          ∀ c : k, (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = scalar (Fin r ⊕ Fin r) c →
            g = 1 :=
  ⟨fun _ hn hnk => even_canonical_identity_isometry_four_group hn hnk,
    fun _ hr => even_canonical_paired_isometry_four_group hr⟩

end CFSG.LocalAnalysis.ComponentInitial
