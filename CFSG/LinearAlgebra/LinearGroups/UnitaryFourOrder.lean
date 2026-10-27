module

public import CFSG.Fischer.F4
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrderSupport
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LinearGroups

open CFSG.LocalAnalysis.ComponentInitial

section StdForm

variable {p f : ℕ} {K : Type*} [Field K]

@[expose] noncomputable def stdHermForm (h : UnitaryFieldData p f K) (n : ℕ) :
    (Fin n → K) →ₛₗ[h.bar] (Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id K) (fun x y => ∑ i, h.bar (x i) * y i)
    (fun x x' y => by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_left_comm])

theorem stdHermForm_apply (h : UnitaryFieldData p f K) (n : ℕ) (x y : Fin n → K) :
    stdHermForm h n x y = ∑ i, h.bar (x i) * y i :=
  rfl

theorem stdHermForm_isSymm (h : UnitaryFieldData p f K) (n : ℕ) : (stdHermForm h n).IsSymm :=
  ⟨fun x y => by
    simp only [stdHermForm_apply, map_sum, map_mul, h.bar_bar]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩

theorem stdHermForm_single (h : UnitaryFieldData p f K) (n : ℕ) (i : Fin n) (y : Fin n → K) :
    stdHermForm h n (Pi.single i 1) y = y i := by
  rw [stdHermForm_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem stdHermForm_separatingLeft (h : UnitaryFieldData p f K) (n : ℕ) :
    (stdHermForm h n).SeparatingLeft := by
  intro x hx
  funext j
  have := hx (Pi.single j 1)
  rw [stdHermForm_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)] at this
  simpa [h.bar_eq_zero_iff] using this

end StdForm

open CFSG.Fischer

theorem unitaryFieldData_F4 : UnitaryFieldData 2 1 F4 :=
  ⟨Nat.prime_two, le_rfl, by rw [Nat.card_eq_fintype_card, F4.card]; norm_num⟩

@[expose] def unitaryFourForm (x y : Fin 4 → F4) : F4 := ∑ i, x i ^ 2 * y i

theorem stdHermForm_F4 (x y : Fin 4 → F4) :
    stdHermForm unitaryFieldData_F4 4 x y = unitaryFourForm x y := by
  simp only [stdHermForm_apply, unitaryFourForm, UnitaryFieldData.bar_apply, pow_one]

theorem sq_eq_frobenius : (fun c : F4 => c ^ 2) = ⇑(frobenius F4 2) := by
  funext c
  rw [frobenius_def]

theorem F4_sq_mul_self_of_ne_zero (c : F4) (hc : c ≠ 0) : c ^ 2 * c = 1 := by
  have := FiniteField.pow_card_sub_one_eq_one c hc
  rw [F4.card] at this
  rw [← pow_succ]
  exact this

@[expose] def unitaryFourGroup : Subgroup (GL (Fin 4) F4) where
  carrier := {A | (A : Matrix (Fin 4) (Fin 4) F4).det = 1 ∧
    ((A : Matrix (Fin 4) (Fin 4) F4).map (· ^ 2)).transpose * A = 1}
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    refine ⟨by rw [Units.val_mul, Matrix.det_mul, hA1, hB1, one_mul], ?_⟩
    rw [sq_eq_frobenius] at hA2 hB2 ⊢
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ (A : Matrix (Fin 4) (Fin 4) F4), hA2, Matrix.one_mul, hB2]
  one_mem' := by
    refine ⟨by rw [Units.val_one, Matrix.det_one], ?_⟩
    rw [sq_eq_frobenius, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one, Matrix.one_mul]
  inv_mem' := by
    rintro A ⟨hA1, hA2⟩
    rw [sq_eq_frobenius] at hA2 ⊢
    have hinv : ((A⁻¹ : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) =
        ((A : Matrix (Fin 4) (Fin 4) F4).map (frobenius F4 2)).transpose := by
      calc ((A⁻¹ : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) =
          ((A : Matrix (Fin 4) (Fin 4) F4).map (frobenius F4 2)).transpose * A *
            ((A⁻¹ : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) := by rw [hA2, Matrix.one_mul]
        _ = _ := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    have hbar : ∀ c : F4, frobenius F4 2 (frobenius F4 2 c) = c := fun c => by
      rw [frobenius_def, frobenius_def]
      exact F4.sq_sq c
    have hmm : ((A : Matrix (Fin 4) (Fin 4) F4).map (frobenius F4 2)).map (frobenius F4 2) =
        A := by
      ext i j
      simp [hbar]
    refine ⟨?_, ?_⟩
    · have h1 := congrArg Matrix.det (show ((A⁻¹ : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) *
          A = 1 by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
      rw [Matrix.det_mul, hA1, mul_one, Matrix.det_one] at h1
      exact h1
    · rw [hinv, Matrix.transpose_map, Matrix.transpose_transpose, hmm]
      exact mul_eq_one_comm.mp hA2

theorem mem_unitaryFourGroup_iff (A : GL (Fin 4) F4) :
    A ∈ unitaryFourGroup ↔ (A : Matrix (Fin 4) (Fin 4) F4).det = 1 ∧
      ((A : Matrix (Fin 4) (Fin 4) F4).map (· ^ 2)).transpose * A = 1 :=
  Iff.rfl

theorem unitary_iff_columns (A : Matrix (Fin 4) (Fin 4) F4) :
    (A.map (· ^ 2)).transpose * A = 1 ↔
      ∀ i j, unitaryFourForm (fun k => A k i) (fun k => A k j) = if i = j then 1 else 0 := by
  constructor
  · intro hA i j
    have := congrFun (congrFun hA i) j
    simpa [Matrix.mul_apply, Matrix.one_apply, unitaryFourForm] using this
  · intro hA
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, unitaryFourForm] using hA i j

@[expose] def unitaryFourDiag (c : F4) : Matrix (Fin 4) (Fin 4) F4 :=
  Matrix.diagonal (Function.update 1 0 c)

theorem unitaryFourDiag_mul (c d : F4) :
    unitaryFourDiag c * unitaryFourDiag d = unitaryFourDiag (c * d) := by
  rw [unitaryFourDiag, unitaryFourDiag, unitaryFourDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst hi
    simp
  · simp [Function.update_of_ne hi]

theorem det_unitaryFourDiag (c : F4) : (unitaryFourDiag c).det = c := by
  rw [unitaryFourDiag, Matrix.det_diagonal, Fin.prod_univ_succ, Function.update_self]
  simp [Fin.succ_ne_zero]

theorem unitary_diag_mul {c : F4} (hc : c ≠ 0) {A : Matrix (Fin 4) (Fin 4) F4}
    (hA : (A.map (· ^ 2)).transpose * A = 1) :
    ((unitaryFourDiag c * A).map (· ^ 2)).transpose * (unitaryFourDiag c * A) = 1 := by
  have hD : ((unitaryFourDiag c).map (frobenius F4 2)).transpose * unitaryFourDiag c = 1 := by
    rw [unitaryFourDiag, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : i = 0
    · subst hi
      rw [Function.update_self, frobenius_def]
      exact F4_sq_mul_self_of_ne_zero c hc
    · simp [Function.update_of_ne hi]
  rw [sq_eq_frobenius] at hA ⊢
  rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (unitaryFourDiag c), hD, Matrix.one_mul, hA]

theorem unitary_four_full_order :
    Nat.card unitaryFourGroup = 25920 ∧
      Nat.card {b : Fin 4 → Fin 4 → F4 //
        ∀ i j, unitaryFourForm (b i) (b j) = if i = j then 1 else 0} = 77760 ∧
      ∀ c : F4, c ≠ 0 → Nat.card {b : Fin 4 → Fin 4 → F4 //
        (∀ i j, unitaryFourForm (b i) (b j) = if i = j then 1 else 0) ∧
          (Matrix.of fun i j => b j i).det = c} = 25920 := by
  classical
  have hframes : Nat.card {b : Fin 4 → Fin 4 → F4 //
      ∀ i j, unitaryFourForm (b i) (b j) = if i = j then 1 else 0} = 77760 := by
    have h1 := card_orthonormalFrames unitaryFieldData_F4 4
      (stdHermForm_isSymm unitaryFieldData_F4 4)
      (stdHermForm_separatingLeft unitaryFieldData_F4 4) (Module.finrank_fin_fun F4)
    have h2 : Nat.card (orthonormalFrames (stdHermForm unitaryFieldData_F4 4) 4) =
        Nat.card {b : Fin 4 → Fin 4 → F4 //
          ∀ i j, unitaryFourForm (b i) (b j) = if i = j then 1 else 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun b => by
        simp only [mem_orthonormalFrames, stdHermForm_F4])
    rw [← h2]
    have h3 : (Nat.card (orthonormalFrames (stdHermForm unitaryFieldData_F4 4) 4) : ℤ) =
        77760 := by
      rw [h1]
      simp [Finset.prod_range_succ]
    exact_mod_cast h3
  let col : {b : Fin 4 → Fin 4 → F4 //
      ∀ i j, unitaryFourForm (b i) (b j) = if i = j then 1 else 0} ≃
      {A : Matrix (Fin 4) (Fin 4) F4 // (A.map (· ^ 2)).transpose * A = 1} :=
    { toFun := fun b => ⟨Matrix.of fun i j => b.1 j i, (unitary_iff_columns _).mpr b.2⟩
      invFun := fun A => ⟨fun j i => A.1 i j, (unitary_iff_columns A.1).mp A.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let N : F4 → ℕ := fun c => Nat.card {A : Matrix (Fin 4) (Fin 4) F4 //
    (A.map (· ^ 2)).transpose * A = 1 ∧ A.det = c}
  have hN0 : N 0 = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨A, hA, hdet⟩ => ?_⟩
    have := congrArg Matrix.det hA
    rw [Matrix.det_mul, hdet, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hdiag1 : unitaryFourDiag 1 = 1 := by
    rw [unitaryFourDiag, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : i = 0
    · subst hi
      simp
    · simp [Function.update_of_ne hi]
  have hNc : ∀ c : F4, c ≠ 0 → N c = N 1 := by
    intro c hc
    have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
    refine Nat.card_congr
      { toFun := fun A => ⟨unitaryFourDiag c⁻¹ * A.1, unitary_diag_mul hc' A.2.1, by
          rw [Matrix.det_mul, det_unitaryFourDiag, A.2.2, inv_mul_cancel₀ hc]⟩
        invFun := fun A => ⟨unitaryFourDiag c * A.1, unitary_diag_mul hc A.2.1, by
          rw [Matrix.det_mul, det_unitaryFourDiag, A.2.2, mul_one]⟩
        left_inv := fun A => Subtype.ext (by
          change unitaryFourDiag c * (unitaryFourDiag c⁻¹ * A.1) = A.1
          rw [← Matrix.mul_assoc, unitaryFourDiag_mul, mul_inv_cancel₀ hc, hdiag1,
            Matrix.one_mul])
        right_inv := fun A => Subtype.ext (by
          change unitaryFourDiag c⁻¹ * (unitaryFourDiag c * A.1) = A.1
          rw [← Matrix.mul_assoc, unitaryFourDiag_mul, inv_mul_cancel₀ hc, hdiag1,
            Matrix.one_mul]) }
  have hsum : Nat.card {A : Matrix (Fin 4) (Fin 4) F4 // (A.map (· ^ 2)).transpose * A = 1} =
      ∑ c : F4, N c := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv fun A :
      {A : Matrix (Fin 4) (Fin 4) F4 // (A.map (· ^ 2)).transpose * A = 1} => A.1.det),
      Nat.card_sigma]
    refine Finset.sum_congr rfl fun c _ => Nat.card_congr ?_
    exact
      { toFun := fun A => ⟨A.1.1, A.1.2, A.2⟩
        invFun := fun A => ⟨⟨A.1, A.2.1⟩, A.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hsum' : ∑ c : F4, N c = 3 * N 1 := by
    rw [Finset.sum_congr rfl fun c _ => show N c = if c = 0 then 0 else N 1 by
      split_ifs with hc
      · rw [hc, hN0]
      · exact hNc c hc]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      F4.card]
  have hN1 : N 1 = 25920 := by
    have := Nat.card_congr col
    rw [hframes, hsum, hsum'] at this
    omega
  have hS : Nat.card unitaryFourGroup = N 1 := by
    refine Nat.card_congr
      { toFun := fun A => ⟨(A.1 : Matrix (Fin 4) (Fin 4) F4), A.2.2, A.2.1⟩
        invFun := fun A => ⟨⟨A.1, (A.1.map (· ^ 2)).transpose,
          mul_eq_one_comm.mp A.2.1, A.2.1⟩, A.2.2, A.2.1⟩
        left_inv := fun A => Subtype.ext (Units.ext rfl)
        right_inv := fun _ => rfl }
  refine ⟨hS.trans hN1, hframes, fun c hc => ?_⟩
  rw [← hN1, ← hNc c hc]
  exact Nat.card_congr
    { toFun := fun b => ⟨Matrix.of fun i j => b.1 j i, (unitary_iff_columns _).mpr b.2.1, b.2.2⟩
      invFun := fun A => ⟨fun j i => A.1 i j, (unitary_iff_columns A.1).mp A.2.1, A.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end CFSG.LinearGroups
