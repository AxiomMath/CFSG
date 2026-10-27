module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aIrred
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open CFSG.QuasithinUnique.Setup.X7

section Distinct

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

theorem iso_torus_char (hF : Fintype.card F = 2 ^ f) {a b a' b' : Fin f → Bool}
    {P : Matrix (TIdx f a' b') (TIdx f a b) k} {Q : Matrix (TIdx f a b) (TIdx f a' b') k}
    (h : MatIso (tensorRep (F := F) k a b) (tensorRep k a' b') P Q) (r t : Fˣ) :
    algebraMap F k (r : F) ^ (mBits a + mBits b) * algebraMap F k (t : F) ^ mBits b =
      algebraMap F k (r : F) ^ (mBits a' + mBits b') * algebraMap F k (t : F) ^ mBits b' := by
  have hmem : hw k a b ∈ fixedSub (matRep (tensorRep (F := F) k a b)) (upperUni F) := by
    rw [(tensorRep_fixed_irreducible k hF a b).1]
    exact Submodule.mem_span_singleton_self _
  have hmem' : P.mulVec (hw k a b) ∈
      fixedSub (matRep (tensorRep (F := F) k a' b')) (upperUni F) := by
    refine mem_fixedSub.mpr fun u hu => ?_
    have h1 := mem_fixedSub.mp hmem u hu
    simp only [matRep_apply] at h1 ⊢
    rw [Matrix.mulVec_mulVec, ← h.comm, ← Matrix.mulVec_mulVec, h1]
  rw [(tensorRep_fixed_irreducible k hF a' b').1] at hmem'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem'
  have hne : P.mulVec (hw k a b) ≠ 0 := by
    intro h0
    have h2 : hw k a b = 0 := by
      have := congrArg Q.mulVec h0
      rwa [Matrix.mulVec_mulVec, h.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact hw_ne_zero k a b h2
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by rw [← hc, zero_smul])
  have e1 : (tensorRep (F := F) k a' b' (dT r t)).mulVec (P.mulVec (hw k a b)) =
      P.mulVec ((tensorRep (F := F) k a b (dT r t)).mulVec (hw k a b)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← h.comm]
  rw [tensorRep_dT_hw k a b r t, Matrix.mulVec_smul, ← hc, Matrix.mulVec_smul,
    tensorRep_dT_hw k a' b' r t, smul_smul, smul_smul] at e1
  have e2 := smul_left_injective k (hw_ne_zero k a' b') e1
  have e3 : c * _ = c * _ := e2.trans (mul_comm _ _)
  exact (mul_left_cancel₀ hc0 e3).symm

theorem iso_weights (hF : Fintype.card F = 2 ^ f) {a b a' b' : Fin f → Bool}
    {P : Matrix (TIdx f a' b') (TIdx f a b) k} {Q : Matrix (TIdx f a b) (TIdx f a' b') k}
    (h : MatIso (tensorRep (F := F) k a b) (tensorRep k a' b') P Q) :
    (mBits a = mBits a' ∨ (mBits a = 0 ∧ mBits a' = 2 ^ f - 1) ∨
        (mBits a' = 0 ∧ mBits a = 2 ^ f - 1)) ∧
      (mBits b = mBits b' ∨ (mBits b = 0 ∧ mBits b' = 2 ^ f - 1) ∨
        (mBits b' = 0 ∧ mBits b = 2 ^ f - 1)) := by
  have hchar := iso_torus_char k hF h
  have hinj : Function.Injective (algebraMap F k) := (algebraMap F k).injective
  have hB : ∀ z : Fˣ, z ^ mBits b = z ^ mBits b' := by
    intro z
    have h1 := hchar 1 z
    simp only [Units.val_one, map_one, one_pow, one_mul] at h1
    exact Units.ext (hinj (by simpa [map_pow] using h1))
  have hAB : ∀ z : Fˣ, z ^ (mBits a + mBits b) = z ^ (mBits a' + mBits b') := by
    intro z
    have h1 := hchar z 1
    simp only [Units.val_one, map_one, one_pow, mul_one] at h1
    exact Units.ext (hinj (by simpa [map_pow] using h1))
  have hA : ∀ z : Fˣ, z ^ mBits a = z ^ mBits a' := by
    intro z
    have h1 := hAB z
    rw [pow_add, pow_add, hB z] at h1
    exact mul_right_cancel h1
  exact ⟨torus_weight_eq hF (mBits_lt a) (mBits_lt a') hA,
    torus_weight_eq hF (mBits_lt b) (mBits_lt b') hB⟩

omit [CharP F 2] [Fintype F] [Algebra F k] [CharP k 2] in
theorem bitsEq_of_weights {a a' : Fin f → Bool}
    (h : mBits a = mBits a' ∨ (mBits a = 0 ∧ mBits a' = 2 ^ f - 1) ∨
      (mBits a' = 0 ∧ mBits a = 2 ^ f - 1)) :
    a = a' ∨ (a = zeros f ∧ a' = ones f) ∨ (a = ones f ∧ a' = zeros f) := by
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (mBits_injective h)
  · exact Or.inr (Or.inl ⟨mBits_eq_zero h1, eq_ones_of_mBits h2⟩)
  · exact Or.inr (Or.inr ⟨eq_ones_of_mBits h2, mBits_eq_zero h1⟩)

end Distinct

section Corners

variable {f : ℕ}

theorem cntS_right_zeros (a : Fin f → Bool) :
    cntS a (zeros f) = (Finset.univ.filter fun i => a i = true).card := by
  unfold cntS zeros
  congr 1
  ext i
  simp

theorem cntH_right_zeros (a : Fin f → Bool) : cntH a (zeros f) = 0 := by
  unfold cntH zeros
  simp

theorem cntS_right_ones (a : Fin f → Bool) :
    cntS a (ones f) + (Finset.univ.filter fun i => a i = true).card = f := by
  have h : (Finset.univ.filter fun i => a i ≠ ones f i) =
      Finset.univ.filter fun i => ¬ (a i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases a i <;> simp [ones]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin f)))
    (fun i => a i = true)
  rw [Finset.card_univ, Fintype.card_fin] at this
  rw [cntS, h, add_comm]
  exact this

theorem cntH_right_ones (a : Fin f → Bool) :
    cntH a (ones f) = (Finset.univ.filter fun i => a i = true).card := by
  unfold cntH ones
  simp

theorem cntS_left_zeros (b : Fin f → Bool) :
    cntS (zeros f) b = (Finset.univ.filter fun i => b i = true).card := by
  unfold cntS zeros
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases b i <;> simp

theorem cntH_left_zeros (b : Fin f → Bool) : cntH (zeros f) b = 0 := by
  unfold cntH zeros
  simp

theorem cntS_left_ones (b : Fin f → Bool) :
    cntS (ones f) b + (Finset.univ.filter fun i => b i = true).card = f := by
  have h : (Finset.univ.filter fun i => ones f i ≠ b i) =
      Finset.univ.filter fun i => ¬ (b i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases b i <;> simp [ones]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin f)))
    (fun i => b i = true)
  rw [Finset.card_univ, Fintype.card_fin] at this
  rw [cntS, h, add_comm]
  exact this

theorem cntH_left_ones (b : Fin f → Bool) :
    cntH (ones f) b = (Finset.univ.filter fun i => b i = true).card := by
  unfold cntH ones
  simp

theorem dim_flip_arith {f J S : ℕ} (hf : 1 ≤ f) (hS : S + J = f) :
    3 ^ J * 8 ^ 0 ≠ 3 ^ S * 8 ^ J := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · have hSf : S = f := by omega
    subst hSf
    have h3 : 3 ≤ 3 ^ S := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ S := Nat.pow_le_pow_right (by norm_num) hf
    simp only [pow_zero, mul_one]
    omega
  · intro h
    have h1 : 2 ∣ 3 ^ S * 8 ^ J :=
      Dvd.dvd.mul_left (dvd_pow (by norm_num : (2 : ℕ) ∣ 8) hJ.ne') _
    rw [← h] at h1
    simp only [pow_zero, mul_one] at h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h1
    omega

theorem bits_cases (hf : 1 ≤ f) {a b a' b' : Fin f → Bool}
    (ha : a = a' ∨ (a = zeros f ∧ a' = ones f) ∨ (a = ones f ∧ a' = zeros f))
    (hb : b = b' ∨ (b = zeros f ∧ b' = ones f) ∨ (b = ones f ∧ b' = zeros f))
    (hdim : 3 ^ cntS a b * 8 ^ cntH a b = 3 ^ cntS a' b' * 8 ^ cntH a' b') :
    (a = a' ∧ b = b') ∨ (a = ones f ∧ b = zeros f ∧ a' = zeros f ∧ b' = ones f) ∨
      (a = zeros f ∧ b = ones f ∧ a' = ones f ∧ b' = zeros f) := by
  rcases ha with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hb with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exfalso
    rw [cntS_right_zeros, cntH_right_zeros, cntH_right_ones] at hdim
    exact dim_flip_arith hf (cntS_right_ones a) hdim
  · exfalso
    rw [cntS_right_zeros, cntH_right_zeros, cntH_right_ones] at hdim
    exact dim_flip_arith hf (cntS_right_ones a) hdim.symm
  · exfalso
    rw [cntS_left_zeros, cntH_left_zeros, cntH_left_ones] at hdim
    exact dim_flip_arith hf (cntS_left_ones b) hdim
  · exfalso
    simp [cntS, cntH, zeros, ones] at hdim
    have := Nat.one_lt_pow (by omega : f ≠ 0) (by norm_num : 1 < 8)
    omega
  · exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
  · exfalso
    rw [cntS_left_zeros, cntH_left_zeros, cntH_left_ones] at hdim
    exact dim_flip_arith hf (cntS_left_ones b) hdim.symm
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  · exfalso
    simp [cntS, cntH, zeros, ones] at hdim
    have := Nat.one_lt_pow (by omega : f ≠ 0) (by norm_num : 1 < 8)
    omega

end Corners

section Trace

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

omit [CharP F 2] [Fintype F] in
theorem trace_tensorRep (a b : Fin f → Bool) (g : SL(3, F)) :
    (tensorRep (F := F) k a b g).trace = ∏ i : Fin f, (locRep k (a i) (b i) (i : ℕ) g).trace := by
  simp only [Matrix.trace, Matrix.diag, tensorRep, tensorRepGen, MonoidHom.coe_mk, OneHom.coe_mk,
    kron_apply]
  have := Finset.prod_univ_sum (fun i : Fin f => (Finset.univ : Finset (Fin (locDim (a i) (b i)))))
    (fun i y => locRep k (a i) (b i) (i : ℕ) g y y)
  simp only [Fintype.piFinset_univ] at this
  exact this.symm

variable (F) in
@[expose] def cSep : SL(3, F) :=
  ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

omit [CharP F 2] [Fintype F] in
theorem trace_natRep_cSep (i : ℕ) : (natRep k i (cSep F)).trace = 0 := by
  simp [natRep, twistMat, Matrix.trace, Fin.sum_univ_three, cSep]

omit [CharP F 2] [Fintype F] in
theorem trace_dualRep_cSep (i : ℕ) : (dualRep k i (cSep F)).trace = 1 := by
  have hc : (((cSep F)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.adjugate !![0, 0, 1; 1, 0, 1; 0, 1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    rfl
  have h1 : dualRep k i (cSep F) = (twistMat k i (cSep F)⁻¹)ᵀ := rfl
  rw [h1, Matrix.trace_transpose]
  simp only [Matrix.trace, Matrix.diag, twistMat_apply, Fin.sum_univ_three, hc]
  simp [Matrix.adjugate_fin_three_of]
  exact CharTwo.neg_eq (1 : k)

omit [CharP F 2] [Fintype F] in
theorem not_iso_natural_dual (hf : 1 ≤ f)
    {P : Matrix (TIdx f (zeros f) (ones f)) (TIdx f (ones f) (zeros f)) k}
    {Q : Matrix (TIdx f (ones f) (zeros f)) (TIdx f (zeros f) (ones f)) k}
    (h : MatIso (tensorRep (F := F) k (ones f) (zeros f)) (tensorRep k (zeros f) (ones f)) P Q) :
    False := by
  have h1 := h.trace_eq (cSep F)
  rw [trace_tensorRep, trace_tensorRep] at h1
  have e1 : ∀ i : Fin f, (locRep k (zeros f i) (ones f i) (i : ℕ) (cSep F)).trace = 1 :=
    fun i => trace_dualRep_cSep k i
  have e0 : ∀ i : Fin f, (locRep k (ones f i) (zeros f i) (i : ℕ) (cSep F)).trace = 0 :=
    fun i => trace_natRep_cSep k i
  rw [Finset.prod_congr rfl (fun i _ => e1 i), Finset.prod_congr rfl (fun i _ => e0 i)] at h1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow] at h1
  rw [zero_pow (by omega)] at h1
  exact one_ne_zero h1

end Trace

section Final

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

theorem tensorRep_eq_of_iso (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {a b a' b' : Fin f → Bool}
    {P : Matrix (TIdx f a' b') (TIdx f a b) k} {Q : Matrix (TIdx f a b) (TIdx f a' b') k}
    (h : MatIso (tensorRep (F := F) k a b) (tensorRep k a' b') P Q) : a = a' ∧ b = b' := by
  obtain ⟨hw1, hw2⟩ := iso_weights k hF h
  have hdim : 3 ^ cntS a b * 8 ^ cntH a b = 3 ^ cntS a' b' * 8 ^ cntH a' b' := by
    rw [← card_TIdx_eq, ← card_TIdx_eq]
    exact h.card_eq
  rcases bits_cases hf (bitsEq_of_weights hw1) (bitsEq_of_weights hw2) hdim with
    h1 | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact h1
  · exact (not_iso_natural_dual k hf h).elim
  · exact (not_iso_natural_dual k hf h.symm).elim

theorem tensorRep_absolutely_irreducible_and_distinct (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) :
    (∀ a b : Fin f → Bool, (matRep (tensorRep (F := F) k a b)).IsIrreducible ∧
        Module.finrank k (TIdx f a b → k) = 3 ^ cntS a b * 8 ^ cntH a b) ∧
      ∀ a b a' b' : Fin f → Bool,
        Nonempty ((matRep (tensorRep (F := F) k a b)).Equiv
          (matRep (tensorRep (F := F) k a' b'))) → a = a' ∧ b = b' := by
  refine ⟨fun a b => ⟨(tensorRep_fixed_irreducible k hF a b).2, ?_⟩, fun a b a' b' ⟨e⟩ => ?_⟩
  · rw [Module.finrank_fintype_fun_eq_card]
    exact card_TIdx_eq a b
  · obtain ⟨P, Q, h⟩ := MatIso.exists_of_equiv e
    exact tensorRep_eq_of_iso k hF hf h

end Final

end CFSG.QuasithinUnique.Setup.X7a
