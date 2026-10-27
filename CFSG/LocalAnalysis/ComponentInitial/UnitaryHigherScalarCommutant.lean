module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {E : Type} [Field E] {m : ℕ}

@[expose] def unitSignDiag (i l : Fin m) : Fin m → E := fun j => if j = i ∨ j = l then -1 else 1

@[expose] def unitLambdaDiag (c : E) (i j : Fin m) : Fin m → E :=
  fun r => if r = i then c else if r = j then c⁻¹ else 1

@[expose] def unitSignedSwap (i j : Fin m) (u : Fin m → E) : Fin m → E :=
  fun r => (if r = i then -1 else 1) * u (Equiv.swap i j r)

@[expose] def unitSignedSwapMatrix (i j : Fin m) : Matrix (Fin m) (Fin m) E :=
  diagonal (fun r => if r = i then -1 else 1) * (Equiv.swap i j).permMatrix E

theorem unitSignedSwapMatrix_mulVec (i j : Fin m) (u : Fin m → E) :
    unitSignedSwapMatrix i j *ᵥ u = unitSignedSwap i j u := by
  rw [unitSignedSwapMatrix, ← mulVec_mulVec, permMatrix_mulVec]
  funext r
  rw [mulVec_diagonal]
  rfl

variable (h : UnitaryFieldData p f E)

theorem mem_gramSU_one_of {M : GL (Fin m) E}
    (hM : ∀ x y, gramForm h (1 : Matrix (Fin m) (Fin m) E) ((M : Matrix (Fin m) (Fin m) E) *ᵥ x)
      ((M : Matrix (Fin m) (Fin m) E) *ᵥ y) = gramForm h 1 x y)
    (hdet : (M : Matrix (Fin m) (Fin m) E).det = 1) : M ∈ gramSU h (1 : Matrix (Fin m) (Fin m) E) :=
  mem_gramSU_iff_isometry.mpr ⟨hM, hdet⟩

theorem diagonal_mem_gramSU_one (d : Fin m → E) (hd : ∀ r, h.bar (d r) * d r = 1)
    (hprod : ∏ r, d r = 1) :
    ∃ M : GL (Fin m) E, (M : Matrix (Fin m) (Fin m) E) = diagonal d ∧
      M ∈ gramSU h (1 : Matrix (Fin m) (Fin m) E) := by
  have hdet : (diagonal d).det = 1 := by rw [det_diagonal, hprod]
  refine ⟨⟨diagonal d, diagonal (fun r => h.bar (d r)), ?_, ?_⟩, rfl, ?_⟩
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext r
    rw [mul_comm, hd r]
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext r
    rw [hd r]
  · refine mem_gramSU_one_of h (fun x y => ?_) hdet
    simp only [gramForm_apply, one_mulVec, mulVec_diagonal, dotProduct, map_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    linear_combination (h.bar (x r) * y r) * hd r

theorem unitSignDiag_mem {i l : Fin m} (hil : i ≠ l) :
    ∃ M : GL (Fin m) E, (M : Matrix (Fin m) (Fin m) E) = diagonal (unitSignDiag i l) ∧
      M ∈ gramSU h (1 : Matrix (Fin m) (Fin m) E) := by
  refine diagonal_mem_gramSU_one h _ (fun r => ?_) ?_
  · by_cases hr : r = i ∨ r = l <;> simp [unitSignDiag, hr]
  · have hfilter : Finset.univ.filter (fun r : Fin m => r = i ∨ r = l) = {i, l} := by
      ext r
      simp
    rw [show (∏ r, unitSignDiag i l r) = ∏ r, (if r = i ∨ r = l then (-1 : E) else 1) from rfl,
      Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, hfilter,
      Finset.card_pair hil, neg_one_sq]

theorem unitLambdaDiag_mem {c : E} (hc : h.bar c * c = 1) {i j : Fin m} (hij : i ≠ j) :
    ∃ M : GL (Fin m) E, (M : Matrix (Fin m) (Fin m) E) = diagonal (unitLambdaDiag c i j) ∧
      M ∈ gramSU h (1 : Matrix (Fin m) (Fin m) E) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact zero_ne_one hc
  refine diagonal_mem_gramSU_one h _ (fun r => ?_) ?_
  · by_cases hri : r = i
    · simp [unitLambdaDiag, hri, hc]
    · by_cases hrj : r = j
      · subst hrj
        have h1 : unitLambdaDiag c i r r = c⁻¹ := by simp [unitLambdaDiag, hri]
        rw [h1, map_inv₀, ← mul_inv, hc, inv_one]
      · simp [unitLambdaDiag, hri, hrj]
  · have hsplit : unitLambdaDiag c i j =
        fun r => (if r = i then c else 1) * (if r = j then c⁻¹ else 1) := by
      funext r
      by_cases hri : r = i
      · subst hri
        simp [unitLambdaDiag, hij]
      · simp [unitLambdaDiag, hri]
    rw [hsplit, Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq',
      mul_inv_cancel₀ hc0]

theorem unitSignedSwapMatrix_mem {i j : Fin m} (hij : i ≠ j) :
    ∃ M : GL (Fin m) E, (M : Matrix (Fin m) (Fin m) E) = unitSignedSwapMatrix i j ∧
      M ∈ gramSU h (1 : Matrix (Fin m) (Fin m) E) := by
  have hdet : (unitSignedSwapMatrix (E := E) i j).det = 1 := by
    rw [unitSignedSwapMatrix, det_mul, det_diagonal, det_permutation, Equiv.Perm.sign_swap hij,
      Fintype.prod_ite_eq']
    simp
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (unitSignedSwapMatrix i j)
    (by rw [hdet]; exact one_ne_zero), rfl,
    mem_gramSU_one_of h (fun x y => ?_) hdet⟩
  change gramForm h 1 (unitSignedSwapMatrix i j *ᵥ x) (unitSignedSwapMatrix i j *ᵥ y) = _
  rw [unitSignedSwapMatrix_mulVec, unitSignedSwapMatrix_mulVec]
  simp only [gramForm_apply, one_mulVec, dotProduct, unitSignedSwap, map_mul]
  have hs : ∀ r : Fin m, h.bar (if r = i then (-1 : E) else 1) *
      (if r = i then (-1 : E) else 1) = 1 := fun r => by
    by_cases hr : r = i <;> simp [hr]
  calc ∑ r, h.bar (if r = i then (-1 : E) else 1) * h.bar (x (Equiv.swap i j r)) *
        ((if r = i then (-1 : E) else 1) * y (Equiv.swap i j r))
      = ∑ r, h.bar (x (Equiv.swap i j r)) * y (Equiv.swap i j r) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        linear_combination (h.bar (x (Equiv.swap i j r)) * y (Equiv.swap i j r)) * hs r
    _ = ∑ r, h.bar (x r) * y r :=
        Equiv.sum_comp (Equiv.swap i j) fun r => h.bar (x r) * y r

omit h in
theorem exists_fin_ne_ne (hm : 3 ≤ m) (i r : Fin m) : ∃ l : Fin m, l ≠ i ∧ l ≠ r := by
  have key : ∀ a : ℕ, a < 3 → a ≠ (i : ℕ) → a ≠ (r : ℕ) → ∃ l : Fin m, l ≠ i ∧ l ≠ r :=
    fun a ha hai har => ⟨⟨a, by omega⟩, fun h0 => hai (congrArg Fin.val h0),
      fun h0 => har (congrArg Fin.val h0)⟩
  by_cases h0 : (0 : ℕ) ≠ i ∧ (0 : ℕ) ≠ r
  · exact key 0 (by norm_num) h0.1 h0.2
  by_cases h1 : (1 : ℕ) ≠ i ∧ (1 : ℕ) ≠ r
  · exact key 1 (by norm_num) h1.1 h1.2
  exact key 2 (by norm_num) (by omega) (by omega)

omit h in
theorem unitSignedSwap_single {i j : Fin m} (hij : i ≠ j) (a : E) :
    unitSignedSwap i j (Pi.single i a) = Pi.single j a := by
  funext r
  simp only [unitSignedSwap]
  by_cases hrj : r = j
  · subst hrj
    simp [Equiv.swap_apply_right, Ne.symm hij]
  · by_cases hri : r = i
    · subst hri
      simp [Equiv.swap_apply_left, hij]
    · simp [Equiv.swap_apply_of_ne_of_ne hri hrj, hri, hrj]

theorem coordinate_commutant_scalar (h2 : (2 : E) ≠ 0) (hm : 3 ≤ m) {c : E}
    (hcN : h.bar c * c = 1) (hck : c ∉ h.fixedField)
    (X : (Fin m → E) →ₗ[h.fixedField] (Fin m → E))
    (hs : ∀ i l : Fin m, i ≠ l → ∀ u,
      X (diagonal (unitSignDiag i l) *ᵥ u) = diagonal (unitSignDiag i l) *ᵥ X u)
    (hd : ∀ i j : Fin m, i ≠ j → ∀ u,
      X (diagonal (unitLambdaDiag c i j) *ᵥ u) = diagonal (unitLambdaDiag c i j) *ᵥ X u)
    (hw : ∀ i j : Fin m, i ≠ j → ∀ u,
      X (unitSignedSwapMatrix i j *ᵥ u) = unitSignedSwapMatrix i j *ᵥ X u) :
    ∃ a : E, ∀ u, X u = a • u := by
  have hsupp : ∀ (i : Fin m) (a : E) (r : Fin m), r ≠ i → X (Pi.single i a) r = 0 := by
    intro i a r hri
    obtain ⟨l, hli, hlr⟩ := exists_fin_ne_ne hm i r
    have h1 := congrFun (hs i l (Ne.symm hli) (Pi.single i a)) r
    have h3 : diagonal (unitSignDiag i l) *ᵥ Pi.single i a = -Pi.single i a := by
      funext r'
      rw [mulVec_diagonal]
      by_cases hr' : r' = i
      · subst hr'
        simp [unitSignDiag]
      · simp [hr']
    have hsr : unitSignDiag i l r = (1 : E) := by simp [unitSignDiag, hri, Ne.symm hlr]
    rw [h3, map_neg, mulVec_diagonal, Pi.neg_apply, hsr, one_mul] at h1
    have h4 : (2 : E) * X (Pi.single i a) r = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h4).resolve_left h2
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcN
    exact zero_ne_one hcN
  have hlam : ∀ (i : Fin m) (a : E), X (Pi.single i (c * a)) = c • X (Pi.single i a) := by
    intro i a
    obtain ⟨j, hji, -⟩ := exists_fin_ne_ne hm i i
    have h1 := hd i j (Ne.symm hji) (Pi.single i a)
    have h3 : diagonal (unitLambdaDiag c i j) *ᵥ Pi.single i a = Pi.single i (c * a) := by
      funext r
      rw [mulVec_diagonal]
      by_cases hr : r = i
      · subst hr
        simp [unitLambdaDiag]
      · simp [hr]
    have h4 : diagonal (unitLambdaDiag c i j) *ᵥ X (Pi.single i a) = c • X (Pi.single i a) := by
      funext r
      rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hr : r = i
      · subst hr
        simp [unitLambdaDiag]
      · rw [hsupp i a r hr, mul_zero, mul_zero]
    rw [h3, h4] at h1
    exact h1
  have hcinv : ∀ (i : Fin m) (a : E), X (Pi.single i (c⁻¹ * a)) = c⁻¹ • X (Pi.single i a) := by
    intro i a
    have h1 := hlam i (c⁻¹ * a)
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hk : ∀ (i : Fin m) (x : h.fixedField) (a : E),
      X (Pi.single i ((x : E) * a)) = (x : E) • X (Pi.single i a) := by
    intro i x a
    have h1 : Pi.single i ((x : E) * a) = x • (Pi.single i a : Fin m → E) := by
      funext r
      rw [Subfield.smul_def, Pi.smul_apply, smul_eq_mul]
      by_cases hr : r = i
      · subst hr
        simp
      · simp [hr]
    rw [h1, map_smul, Subfield.smul_def]
  have hbarc : h.bar c = c⁻¹ := eq_inv_of_mul_eq_one_left hcN
  have ht : h.bar (c - c⁻¹) = -(c - c⁻¹) := by
    rw [map_sub, map_inv₀, hbarc, inv_inv, neg_sub]
  have ht0 : c - c⁻¹ ≠ 0 := by
    intro h0
    apply hck
    have h1 : c * c = 1 := by
      have h3 : c = c⁻¹ := sub_eq_zero.mp h0
      calc c * c = c * c⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel₀ hc0
    rcases mul_self_eq_one_iff.mp h1 with h3 | h3
    · rw [h3]
      exact one_mem _
    · rw [h3]
      exact neg_mem (one_mem _)
  have htline : ∀ (i : Fin m) (a : E),
      X (Pi.single i ((c - c⁻¹) * a)) = (c - c⁻¹) • X (Pi.single i a) := by
    intro i a
    rw [sub_mul, Pi.single_sub, map_sub, hlam, hcinv, sub_smul]
  have hE : ∀ (i : Fin m) (b a : E), X (Pi.single i (b * a)) = b • X (Pi.single i a) := by
    intro i b a
    obtain ⟨hx, hy, hb⟩ := scalar_decomp ht ht0 h2 b
    obtain ⟨x, hxdef⟩ : ∃ x : h.fixedField, (x : E) = 2⁻¹ * (b + h.bar b) := ⟨⟨_, hx⟩, rfl⟩
    obtain ⟨y, hydef⟩ : ∃ y : h.fixedField, (y : E) = (2 * (c - c⁻¹))⁻¹ * (b - h.bar b) :=
      ⟨⟨_, hy⟩, rfl⟩
    rw [← hxdef, ← hydef] at hb
    rw [hb, add_mul, Pi.single_add, map_add, add_smul, mul_assoc (c - c⁻¹) (y : E) a, htline,
      hk i x a, hk i y a, mul_smul]
  have hline : ∀ i : Fin m, X (Pi.single i 1) = Pi.single i (X (Pi.single i 1) i) := by
    intro i
    funext r
    by_cases hr : r = i
    · subst hr
      simp
    · simp [hsupp i 1 r hr, hr]
  have heq : ∀ i j : Fin m, X (Pi.single j 1) j = X (Pi.single i 1) i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have h1 := hw i j hij (Pi.single i 1)
    rw [unitSignedSwapMatrix_mulVec, unitSignedSwapMatrix_mulVec, unitSignedSwap_single hij,
      hline i, unitSignedSwap_single hij] at h1
    have h3 := congrFun h1 j
    simpa using h3
  refine ⟨X (Pi.single ⟨0, by omega⟩ 1) ⟨0, by omega⟩, fun u => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single u]
  rw [map_sum]
  conv_rhs => rw [← Finset.univ_sum_single u]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have e1 := hE r (u r) 1
  rw [mul_one] at e1
  rw [e1, hline r, heq ⟨0, by omega⟩ r]
  funext s
  by_cases hs : s = r
  · subst hs
    simp [mul_comm]
  · simp [hs]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
