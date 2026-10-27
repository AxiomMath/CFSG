module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4Core
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

namespace GenLocL4Gen4U

open GenLocL4Gen4

variable {p f : ℕ} {K : Type} [Field K]

theorem blk_map (σ : K →+* K) (A B : Matrix (Fin 2) (Fin 2) K) :
    (blk A B).map σ = blk (A.map σ) (B.map σ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blk]

theorem blk_transpose (A B : Matrix (Fin 2) (Fin 2) K) : (blk A B)ᵀ = blk Aᵀ Bᵀ := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blk]

variable (h : UnitaryFieldData p f K)

theorem bar_eq_neg {i : K} (hi : i * i = -1) (hq : p ^ f % 4 = 3) : h.bar i = -i := by
  rw [h.bar_apply]
  obtain ⟨a, ha⟩ : ∃ a, p ^ f = 4 * a + 3 := ⟨p ^ f / 4, by omega⟩
  have h4 : i ^ 4 = 1 := by
    calc i ^ 4 = (i * i) * (i * i) := by ring
      _ = 1 := by rw [hi]; ring
  rw [ha, pow_add, pow_mul, h4, one_pow, one_mul]
  linear_combination i * hi

theorem blk_unitary {A B : Matrix (Fin 2) (Fin 2) K} (hA : (A.map h.bar)ᵀ * A = 1)
    (hB : (B.map h.bar)ᵀ * B = 1) : ((blk A B).map h.bar)ᵀ * blk A B = 1 := by
  rw [blk_map, blk_transpose, blk_mul, hA, hB, blk_one]

variable {i : K} (hi : i * i = -1) (hbar : h.bar i = -i)

include hbar

theorem unitary_gZR : (((gZR i hi : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
    ((gZR i hi : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gZR, hbar, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination (-1 : K) * hi

theorem unitary_gXR : (((gXR i hi : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
    ((gXR i hi : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gXR, hbar, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination (-1 : K) * hi

theorem unitary_gR : (((gR i hi : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
    ((gR i hi : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gR, hbar, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination (-1 : K) * hi

omit hbar in
theorem unitary_one : (((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
    ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  simp

theorem K₀_le_unitary : K₀ i hi ≤
    (primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).comap Θ := by
  rw [K₀, closure_le]
  intro x hx
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have key : ∀ A B : GL (Fin 2) K, ((A : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * A = 1 →
      ((B : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * B = 1 →
      (A, B) ∈ ((primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).comap Θ :
        Set (GL (Fin 2) K × GL (Fin 2) K)) := by
    intro A B hA hB
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_primeFormUnitary, Θ_val, Units.val_one,
      Matrix.mul_one]
    exact blk_unitary h hA hB
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact key _ _ (unitary_gZR h hi hbar) (unitary_one h)
  · exact key _ _ (unitary_gXR h hi hbar) (unitary_one h)
  · exact key _ _ (unitary_one h) (unitary_gZR h hi hbar)
  · exact key _ _ (unitary_one h) (unitary_gXR h hi hbar)
  · exact key _ _ (unitary_gR h hi hbar) (unitary_one h)

omit hbar

theorem conjHom_mem_of_det (C : Matrix (Fin 4) (Fin 4) K) (A t : primeFormUnitary h C)
    (hA : ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 ∨
      ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = -1)
    (ht : ((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = -1) :
    primeFormConjHom h C A ∈ (MulAut.conj : primeFormP h C →* MulAut (primeFormP h C)).range ⊔
      zpowers (primeFormConjHom h C t) := by
  have hinner : ∀ B : primeFormUnitary h C, ((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 →
      primeFormConjHom h C B ∈ (MulAut.conj : primeFormP h C →* MulAut (primeFormP h C)).range := by
    intro B hB
    have hs : (B : GL (Fin 4) K) ∈ gramSU h C := (mem_gramSU_iff_unitary h).2 ⟨B.2, hB⟩
    exact ⟨_, (primeFormConjHom_eq_conj h C ⟨B, hs⟩).symm⟩
  rcases hA with hA | hA
  · exact Subgroup.mem_sup_left (hinner A hA)
  · have h1 : (((A * t⁻¹ : primeFormUnitary h C) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
      have h2 : (((t⁻¹ : primeFormUnitary h C) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det *
          ((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          Units.val_one, Matrix.det_one]
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, hA]
      rw [ht] at h2
      linear_combination h2
    have h3 : primeFormConjHom h C A =
        primeFormConjHom h C (A * t⁻¹) * primeFormConjHom h C t := by
      rw [← map_mul, inv_mul_cancel_right]
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hinner _ h1))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin 4) K) := by
  refine ⟨by rw [Units.val_one, transpose_one], fun i j => ?_⟩
  rw [Units.val_one, one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) in
@[expose] def refl4U : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
  ⟨refl4 K, by
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, coe_refl4,
      Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    ext a b
    fin_cases a <;> fin_cases b <;> simp⟩

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) in
theorem coe_refl4U : (((refl4U h : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![-1, 1, 1, 1] := rfl

end GenLocL4Gen4U

open GenLocL4Gen4 GenLocL4Gen4U in
theorem not_sectional_u4_t1 {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : p ^ f % 8 = 3) (t : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (ht : ((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![-1, 1, 1, 1]) :
    ¬ SectionalTwoRankLE ↥((MulAut.conj : primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) →*
        MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))).range ⊔
      zpowers (primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) t)) 4 := by
  have hfin : Finite K := h.finite
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ^ f % 2 = 0 := by
      have := h.one_le
      exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
    omega
  have hchar : ringChar K ≠ 2 := by
    have := h.charP
    rw [ringChar.eq K p]
    exact hp2
  have hne : (-1 : K) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hchar
  obtain ⟨i, hi⟩ : ∃ i : K, i * i = -1 := by
    have := Fintype.ofFinite K
    have h4 : Fintype.card K % 4 ≠ 3 := by
      rw [← Nat.card_eq_fintype_card, h.card, pow_mul', Nat.pow_mod]
      have : (p ^ f) % 4 = 3 := by omega
      rw [this]
      norm_num
    obtain ⟨r, hr⟩ := FiniteField.isSquare_neg_one_iff.2 h4
    exact ⟨r, hr.symm⟩
  have hbar : h.bar i = -i := bar_eq_neg h hi (by omega)
  have hdt : ((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = -1 := by
    rw [ht, Matrix.det_diagonal]
    simp [Fin.prod_univ_four]
  have hC : IsPrimeFormGram (1 : GL (Fin 4) K) := isPrimeFormGram_one
  have : Finite (MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))) :=
    Finite.of_injective (fun α : MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) =>
      (α : _ → _)) fun _ _ hα => MulEquiv.ext (congrFun hα)
  let ΘU : K₀ i hi →* primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    (Θ.comp (K₀ i hi).subtype).codRestrict _ (fun k => K₀_le_unitary h hi hbar k.2)
  refine not_sectionalTwoRankLE_of_char _ ((primeFormConjHom h _).comp ΘU)
    (fun k => conjHom_mem_of_det h _ (ΘU k) t (det_Θ_eq i hi k) hdt) (psi i hi) (psi_sq i hi) ?_
    (r := 4) (by have := card_range_psi i hi hne; omega)
  intro k hk
  have hk' : primeFormConjHom h _ (ΘU k) = 1 := hk
  have key := (primeFormPsi_eq_one_iff h hC (by norm_num : 3 ≤ 4) ⟨ΘU k, 1⟩).1
    (by rw [primeFormPsi_apply, map_one, mul_one]; exact hk')
  obtain ⟨-, c, hcn, hc⟩ := key
  have hcq : (c : K) ^ (p ^ f + 1) = 1 := by
    have := hcn
    rw [UnitaryFieldData.norm, h.bar_apply, ← pow_succ'] at this
    exact this
  exact psi_eq_one_of_scalar i hi k c hc (pow_four_ne_neg_one (m := p ^ f + 1) (by omega) hne hcq)

end CFSG.GH74.Generic.BProg.B2
