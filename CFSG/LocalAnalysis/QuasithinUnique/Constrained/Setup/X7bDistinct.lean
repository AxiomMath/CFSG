module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bInvol

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7
open CFSG.QuasithinUnique.Setup.X7a (mBits mBits_lt mBits_injective mBits_zeros mBits_eq_zero
  mBits_ones eq_ones_of_mBits torus_weight_eq zeros ones)

section Bits

variable {f : ℕ}

@[expose] def evenBits (f : ℕ) (A : Finset ℕ) : Fin f → Bool := fun j => decide (2 * (j : ℕ) ∈ A)

@[expose] def oddBits (f : ℕ) (A : Finset ℕ) : Fin f → Bool :=
  fun j => decide (2 * (j : ℕ) + 1 ∈ A)

@[expose] def cntBits (a : Fin f → Bool) : ℕ := (Finset.univ.filter fun j => a j = true).card

theorem mIdx_eq_mBits (A : Finset ℕ) : mIdx f A = mBits (evenBits f A) := by
  rw [mIdx, mBits, Finset.sum_range (fun j => if 2 * j ∈ A then 2 ^ j else 0)]
  simp [evenBits]

theorem nIdx_eq_mBits (A : Finset ℕ) : nIdx f A = mBits (oddBits f A) := by
  rw [nIdx, mBits, Finset.sum_range (fun j => if 2 * j + 1 ∈ A then 2 ^ j else 0)]
  simp [oddBits]

theorem cntBits_zeros : cntBits (zeros f) = 0 := by
  simp [cntBits, zeros]

theorem cntBits_ones : cntBits (ones f) = f := by
  simp [cntBits, ones]

theorem card_eq_cnt {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f)) :
    A.card = cntBits (evenBits f A) + cntBits (oddBits f A) := by
  classical
  have h1 : A.card = ∑ i ∈ Finset.range (2 * f), (if i ∈ A then 1 else 0) := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hA]
    simp
  rw [h1, sum_range_two_add, Finset.sum_add_distrib]
  congr 1
  · rw [cntBits, Finset.card_filter, Finset.sum_range (fun j => if 2 * j ∈ A then 1 else 0)]
    simp [evenBits]
  · rw [cntBits, Finset.card_filter, Finset.sum_range (fun j => if 2 * j + 1 ∈ A then 1 else 0)]
    simp [oddBits]

theorem eq_of_bits {A B : Finset ℕ} (hA : A ⊆ Finset.range (2 * f)) (hB : B ⊆ Finset.range (2 * f))
    (he : evenBits f A = evenBits f B) (ho : oddBits f A = oddBits f B) : A = B := by
  ext i
  by_cases hi : i < 2 * f
  · obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · have hj : j < f := by omega
      have := congrFun he ⟨j, hj⟩
      simpa [evenBits] using this
    · have hj : j < f := by omega
      have := congrFun ho ⟨j, hj⟩
      simpa [oddBits] using this
  · constructor <;> intro h
    · exact absurd (Finset.mem_range.mp (hA h)) hi
    · exact absurd (Finset.mem_range.mp (hB h)) hi

theorem bitsEq_of_weights {a a' : Fin f → Bool}
    (h : mBits a = mBits a' ∨ (mBits a = 0 ∧ mBits a' = 2 ^ f - 1) ∨
      (mBits a' = 0 ∧ mBits a = 2 ^ f - 1)) :
    a = a' ∨ (a = zeros f ∧ a' = ones f) ∨ (a = ones f ∧ a' = zeros f) := by
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (mBits_injective h)
  · exact Or.inr (Or.inl ⟨mBits_eq_zero h1, eq_ones_of_mBits h2⟩)
  · exact Or.inr (Or.inr ⟨eq_ones_of_mBits h2, mBits_eq_zero h1⟩)

end Bits

section Distinct

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

theorem iso_torus_char (hF : Fintype.card F = 2 ^ f) {A B : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * f)) (hB : B ⊆ Finset.range (2 * f))
    {P : Matrix (B → Fin 4) (A → Fin 4) k} {Q : Matrix (A → Fin 4) (B → Fin 4) k}
    (h : MatIso (tensorRepS (F := F) k A) (tensorRepS k B) P Q) (s t : Fˣ) :
    algebraMap F k (s : F) ^ (mIdx f A + nIdx f A) * algebraMap F k (t : F) ^ nIdx f A =
      algebraMap F k (s : F) ^ (mIdx f B + nIdx f B) * algebraMap F k (t : F) ^ nIdx f B := by
  obtain ⟨hfixA, -⟩ := tensorRepS_fixed_irreducible k hF hA
  obtain ⟨hfixB, -⟩ := tensorRepS_fixed_irreducible k hF hB
  have hmem : hwS k A ∈ fixedSub (matRep (tensorRepS (F := F) k A)) (upperUniSp F) := by
    rw [hfixA]
    exact Submodule.mem_span_singleton_self _
  have hmem' : P.mulVec (hwS k A) ∈
      fixedSub (matRep (tensorRepS (F := F) k B)) (upperUniSp F) := by
    refine mem_fixedSub.mpr fun u hu => ?_
    have h1 := mem_fixedSub.mp hmem u hu
    simp only [matRep_apply] at h1 ⊢
    rw [Matrix.mulVec_mulVec, ← h.comm, ← Matrix.mulVec_mulVec, h1]
  rw [hfixB] at hmem'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem'
  have hne : P.mulVec (hwS k A) ≠ 0 := by
    intro h0
    have h2 : hwS k A = 0 := by
      have := congrArg Q.mulVec h0
      rwa [Matrix.mulVec_mulVec, h.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact hwS_ne_zero k A h2
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by rw [← hc, zero_smul])
  have e1 : (tensorRepS (F := F) k B (dSp s t)).mulVec (P.mulVec (hwS k A)) =
      P.mulVec ((tensorRepS (F := F) k A (dSp s t)).mulVec (hwS k A)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← h.comm]
  rw [(squarefree_tensor_fixed_line_and_character k hF hA).2.2.2 s t, Matrix.mulVec_smul, ← hc,
    Matrix.mulVec_smul, (squarefree_tensor_fixed_line_and_character k hF hB).2.2.2 s t, smul_smul,
    smul_smul] at e1
  have e2 := smul_left_injective k (hwS_ne_zero k B) e1
  have e3 : c * _ = c * _ := e2.trans (mul_comm _ _)
  exact (mul_left_cancel₀ hc0 e3).symm

theorem iso_weights (hF : Fintype.card F = 2 ^ f) {A B : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * f)) (hB : B ⊆ Finset.range (2 * f))
    {P : Matrix (B → Fin 4) (A → Fin 4) k} {Q : Matrix (A → Fin 4) (B → Fin 4) k}
    (h : MatIso (tensorRepS (F := F) k A) (tensorRepS k B) P Q) :
    (mBits (evenBits f A) = mBits (evenBits f B) ∨
        (mBits (evenBits f A) = 0 ∧ mBits (evenBits f B) = 2 ^ f - 1) ∨
        (mBits (evenBits f B) = 0 ∧ mBits (evenBits f A) = 2 ^ f - 1)) ∧
      (mBits (oddBits f A) = mBits (oddBits f B) ∨
        (mBits (oddBits f A) = 0 ∧ mBits (oddBits f B) = 2 ^ f - 1) ∨
        (mBits (oddBits f B) = 0 ∧ mBits (oddBits f A) = 2 ^ f - 1)) := by
  have hchar := iso_torus_char k hF hA hB h
  have hinj : Function.Injective (algebraMap F k) := (algebraMap F k).injective
  have hN : ∀ z : Fˣ, z ^ nIdx f A = z ^ nIdx f B := by
    intro z
    have h1 := hchar 1 z
    simp only [Units.val_one, map_one, one_pow, one_mul] at h1
    exact Units.ext (hinj (by simpa [map_pow] using h1))
  have hMN : ∀ z : Fˣ, z ^ (mIdx f A + nIdx f A) = z ^ (mIdx f B + nIdx f B) := by
    intro z
    have h1 := hchar z 1
    simp only [Units.val_one, map_one, one_pow, mul_one] at h1
    exact Units.ext (hinj (by simpa [map_pow] using h1))
  have hM : ∀ z : Fˣ, z ^ mIdx f A = z ^ mIdx f B := by
    intro z
    have h1 := hMN z
    rw [pow_add, pow_add, hN z] at h1
    exact mul_right_cancel h1
  simp only [mIdx_eq_mBits] at hM
  simp only [nIdx_eq_mBits] at hN
  exact ⟨torus_weight_eq hF (mBits_lt _) (mBits_lt _) hM,
    torus_weight_eq hF (mBits_lt _) (mBits_lt _) hN⟩

theorem all_even_of_oddBits_zeros {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f))
    (h : oddBits f A = zeros f) : ∀ i ∈ A, i % 2 = 0 := by
  intro i hi
  by_contra hodd
  have hlt : i < 2 * f := Finset.mem_range.mp (hA hi)
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · omega
  · have hj : j < f := by omega
    have := congrFun h ⟨j, hj⟩
    simp [oddBits, zeros, hi] at this

theorem exists_odd_of_oddBits_ones (hf : 1 ≤ f) {B : Finset ℕ} (h : oddBits f B = ones f) :
    ∃ i ∈ B, i % 2 = 1 := by
  have := congrFun h ⟨0, hf⟩
  simp [oddBits, ones] at this
  exact ⟨1, this, rfl⟩

omit [CharP k 2] in
theorem rank_iso_invX {A B : Finset ℕ} {P : Matrix (B → Fin 4) (A → Fin 4) k}
    {Q : Matrix (A → Fin 4) (B → Fin 4) k}
    (h : MatIso (tensorRepS (F := F) k A) (tensorRepS k B) P Q) :
    (tensorRepS k B (invX F) - 1).rank = (tensorRepS k A (invX F) - 1).rank := by
  have h1 : tensorRepS k B (invX F) = P * tensorRepS k A (invX F) * Q := by
    calc tensorRepS k B (invX F) = tensorRepS k B (invX F) * (P * Q) := by
          rw [h.mul_inv, Matrix.mul_one]
      _ = (tensorRepS k B (invX F) * P) * Q := by rw [Matrix.mul_assoc]
      _ = P * tensorRepS k A (invX F) * Q := by rw [← h.comm]
  have h2 : tensorRepS k B (invX F) - 1 = P * (tensorRepS k A (invX F) - 1) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h.mul_inv, ← h1]
  rw [h2, rank_conj_eq _ _ _ h.inv_mul]

theorem not_iso_even_odd {A B : Finset ℕ} {P : Matrix (B → Fin 4) (A → Fin 4) k}
    {Q : Matrix (A → Fin 4) (B → Fin 4) k}
    (h : MatIso (tensorRepS (F := F) k A) (tensorRepS k B) P Q) (hAe : ∀ i ∈ A, i % 2 = 0)
    (hBo : ∃ i ∈ B, i % 2 = 1) (hcard : A.card = B.card) (hm : 1 ≤ A.card) : False := by
  have e1 := rank_tensorRepS_invX (F := F) k A
  have e2 := rank_tensorRepS_invX (F := F) k B
  have hnot : ¬ ∀ i ∈ B, i % 2 = 0 := by
    push Not
    obtain ⟨i, hi, hi'⟩ := hBo
    exact ⟨i, hi, by omega⟩
  have hc1 : (∀ i ∈ A, i % 2 = 0) = True := eq_true hAe
  have hc2 : (∀ i ∈ B, i % 2 = 0) = False := eq_false hnot
  simp only [hc1, ite_true] at e1
  simp only [hc2, ite_false] at e2
  rw [← hcard] at e2
  have hr := rank_iso_invX k h
  rw [e1, e2] at hr
  have h2 : 2 ≤ 2 ^ A.card := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ A.card := Nat.pow_le_pow_right (by norm_num) hm
  have hle : 2 ^ A.card ≤ 4 ^ A.card := Nat.pow_le_pow_left (by norm_num) _
  have h2e : 2 ∣ 2 ^ A.card := dvd_pow_self 2 (by omega)
  have h4e : 2 ∣ 4 ^ A.card := dvd_pow (by norm_num) (by omega)
  omega

end Distinct

section Final

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

theorem tensorRepS_eq_of_iso (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {A B : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * f)) (hB : B ⊆ Finset.range (2 * f))
    {P : Matrix (B → Fin 4) (A → Fin 4) k} {Q : Matrix (A → Fin 4) (B → Fin 4) k}
    (h : MatIso (tensorRepS (F := F) k A) (tensorRepS k B) P Q) : A = B := by
  obtain ⟨hw1, hw2⟩ := iso_weights k hF hA hB h
  have hdim : A.card = B.card := by
    have h1 := h.card_eq
    simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] at h1
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h1
  have hcnt : cntBits (evenBits f A) + cntBits (oddBits f A) =
      cntBits (evenBits f B) + cntBits (oddBits f B) := by
    rw [← card_eq_cnt hA, ← card_eq_cnt hB]
    exact hdim
  have hcA := card_eq_cnt hA
  have hcB := card_eq_cnt hB
  rcases bitsEq_of_weights hw1 with he | ⟨he1, he2⟩ | ⟨he1, he2⟩ <;>
    rcases bitsEq_of_weights hw2 with ho | ⟨ho1, ho2⟩ | ⟨ho1, ho2⟩
  · exact eq_of_bits hA hB he ho
  · exfalso
    rw [he, ho1, ho2, cntBits_zeros, cntBits_ones] at hcnt
    omega
  · exfalso
    rw [he, ho1, ho2, cntBits_zeros, cntBits_ones] at hcnt
    omega
  · exfalso
    rw [ho, he1, he2, cntBits_zeros, cntBits_ones] at hcnt
    omega
  · exfalso
    rw [he1, he2, ho1, ho2, cntBits_zeros, cntBits_ones] at hcnt
    omega
  ·
    exfalso
    have hBe := all_even_of_oddBits_zeros hB ho2
    have hAo := exists_odd_of_oddBits_ones hf ho1
    rw [he1, ho1, cntBits_zeros, cntBits_ones] at hcA
    rw [he2, ho2, cntBits_zeros, cntBits_ones] at hcB
    exact not_iso_even_odd k h.symm hBe hAo (by omega) (by omega)
  · exfalso
    rw [ho, he1, he2, cntBits_zeros, cntBits_ones] at hcnt
    omega
  ·
    exfalso
    have hAe := all_even_of_oddBits_zeros hA ho1
    have hBo := exists_odd_of_oddBits_ones hf ho2
    rw [he1, ho1, cntBits_zeros, cntBits_ones] at hcA
    rw [he2, ho2, cntBits_zeros, cntBits_ones] at hcB
    exact not_iso_even_odd k h hAe hBo (by omega) (by omega)
  · exfalso
    rw [he1, he2, ho1, ho2, cntBits_zeros, cntBits_ones] at hcnt
    omega

theorem tensorRepS_absolutely_irreducible_and_distinct (hF : Fintype.card F = 2 ^ f)
    (hf : 1 ≤ f) :
    (∀ A : Finset ℕ, A ⊆ Finset.range (2 * f) →
        (matRep (tensorRepS (F := F) k A)).IsIrreducible ∧
          Module.finrank k ((A → Fin 4) → k) = 4 ^ A.card) ∧
      ∀ A : Finset ℕ, A ⊆ Finset.range (2 * f) → ∀ B : Finset ℕ, B ⊆ Finset.range (2 * f) →
        Nonempty ((matRep (tensorRepS (F := F) k A)).Equiv
          (matRep (tensorRepS (F := F) k B))) → A = B := by
  refine ⟨fun A hA => ⟨(tensorRepS_fixed_irreducible k hF hA).2, finrank_tensorRepS k A⟩,
    fun A hA B hB ⟨e⟩ => ?_⟩
  obtain ⟨P, Q, h⟩ := MatIso.exists_of_equiv e
  exact tensorRepS_eq_of_iso k hF hf hA hB h

end Final

end CFSG.QuasithinUnique.Setup.X7b
