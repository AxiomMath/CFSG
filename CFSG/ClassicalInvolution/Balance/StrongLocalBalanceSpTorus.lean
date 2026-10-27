module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpNormal

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

theorem tens_map (σ : F ≃+* F) (m n : Matrix (Fin 2) (Fin 2) F) :
    (tens m n).map σ = tens (m.map σ) (n.map σ) := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;> simp [tens, Matrix.fromBlocks]

@[expose] def upSL (c : F) : SL(2, F) := ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def loSL (c : F) : SL(2, F) := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def Nup : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := Matrix.fromBlocks 0 1 0 0

@[expose] def Nlo : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := Matrix.fromBlocks 0 0 1 0

theorem tens_upSL (c : F) : tens (upSL c : Matrix (Fin 2) (Fin 2) F) 1 = 1 + c • Nup := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [tens, upSL, Nup, Matrix.fromBlocks]

theorem tens_loSL (c : F) : tens (loSL c : Matrix (Fin 2) (Fin 2) F) 1 = 1 + c • Nlo := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [tens, loSL, Nlo, Matrix.fromBlocks]

theorem map_upSL (σ : F ≃+* F) (c : F) :
    (upSL c : Matrix (Fin 2) (Fin 2) F).map σ = (upSL (σ c) : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upSL]

theorem eq_tens_one_of_commute {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hU : A * Nup = Nup * A) (hL : A * Nlo = Nlo * A) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, A = tens 1 P := by
  obtain ⟨P, Q, R, S, rfl⟩ : ∃ P Q R S, A = Matrix.fromBlocks P Q R S :=
    ⟨A.toBlocks₁₁, A.toBlocks₁₂, A.toBlocks₂₁, A.toBlocks₂₂, (Matrix.fromBlocks_toBlocks A).symm⟩
  simp only [Nup, Nlo, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hU hL
  simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at hU hL
  obtain ⟨-, hPS, -, hR⟩ := hU
  obtain ⟨hQ, -, hSP, -⟩ := hL
  refine ⟨P, ?_⟩
  rw [← hSP, hR, hQ]
  simp [tens, Matrix.fromBlocks]

theorem rigid_Δsl (σ : F ≃+* F) {A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hBA : B * A = 1)
    (h : ∀ h : SL(2, F), A * (tens (h : Matrix (Fin 2) (Fin 2) F) 1).map σ =
      tens (h : Matrix (Fin 2) (Fin 2) F) 1 * A) :
    (∀ c, σ c = c) ∧ ∃ P : Matrix (Fin 2) (Fin 2) F, A = tens 1 P := by
  have hone : (1 : Matrix (Fin 2) (Fin 2) F).map σ = 1 := Matrix.map_one σ (map_zero σ) (map_one σ)
  have hup : ∀ c, σ c • (A * Nup) = c • (Nup * A) := by
    intro c
    have := h (upSL c)
    rw [tens_map, map_upSL, hone, tens_upSL, tens_upSL, mul_add, add_mul, mul_one, one_mul,
      Matrix.mul_smul, Matrix.smul_mul] at this
    exact add_left_cancel this
  have hNup : A * Nup = Nup * A := by simpa using hup 1
  have hσ : ∀ c, σ c = c := by
    intro c
    by_contra hne
    have h1 : (σ c - c) • (A * Nup) = 0 := by
      rw [sub_smul, hup c, ← hNup, sub_self]
    have h2 : A * Nup = 0 := (smul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hne)
    have h3 : (Nup : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 0 := by
      calc (Nup : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (B * A) * Nup := by rw [hBA, one_mul]
        _ = B * (A * Nup) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [h2, mul_zero]
    have := congrFun (congrFun h3 (Sum.inl 0)) (Sum.inr 0)
    simp [Nup] at this
  have hmap : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F, M.map σ = M := fun M => by
    ext i j
    simp [hσ]
  have hNlo : A * Nlo = Nlo * A := by
    have := h (loSL 1)
    rw [hmap, tens_loSL, one_smul, mul_add, add_mul, mul_one, one_mul] at this
    exact add_left_cancel this
  exact ⟨hσ, eq_tens_one_of_commute hNup hNlo⟩

theorem transpose_mul_eq {B : Matrix (Fin 2) (Fin 2) F} {μ : F}
    (h : (tens 1 B)ᵀ * gram F 2 * tens 1 B = μ • gram F 2) : Bᵀ * B = μ • 1 := by
  rw [tens_transpose, gram_eq_tens, Matrix.transpose_one, tens_mul, tens_mul, one_mul, mul_one,
    mul_one, ← tens_smul_right] at h
  ext i j
  have := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
  simpa [tens, J0] using this

@[expose] def reflM (p r : F) : Matrix (Fin 2) (Fin 2) F := !![p, r; r, -p]

theorem classify_orthogonal {B : Matrix (Fin 2) (Fin 2) F} {μ : F} (hμ : μ ≠ 0)
    (h : Bᵀ * B = μ • 1) :
    (∃ p r : F, B = p • 1 + r • Rot) ∨ (∃ p r : F, B = reflM p r ∧ p ^ 2 + r ^ 2 = μ) := by
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s, B = !![p, q; r, s] :=
    ⟨B 0 0, B 0 1, B 1 0, B 1 1, Matrix.eta_fin_two B⟩
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  have hD : (p * s - q * r) ^ 2 = μ ^ 2 := by
    linear_combination (q * q + s * s) * e00 + μ * e11 - (p * q + r * s) * e01
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hD with hD | hD
  · left
    have hs : s = p := mul_right_cancel₀ hμ (by linear_combination p * hD + r * e01 - s * e00)
    have hq : q = -r := by
      have : (q + r) * μ = 0 := by linear_combination (-r) * hD + p * e01 - q * e00
      linear_combination (mul_eq_zero.mp this).resolve_right hμ
    refine ⟨p, r, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Rot, hs, hq]
  · right
    have hs : s = -p := by
      have : (s + p) * μ = 0 := by linear_combination p * hD + r * e01 - s * e00
      linear_combination (mul_eq_zero.mp this).resolve_right hμ
    have hq : q = r := by
      have : (q - r) * μ = 0 := by linear_combination (-r) * hD + p * e01 - q * e00
      linear_combination (mul_eq_zero.mp this).resolve_right hμ
    refine ⟨p, r, ?_, by linear_combination e00⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [reflM, hs, hq]

theorem tens_right_injective {m : Matrix (Fin 2) (Fin 2) F} (hm : m 0 0 = 1)
    {n n' : Matrix (Fin 2) (Fin 2) F} (h : tens m n = tens m n') : n = n' := by
  ext i j
  have := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  simpa [tens, hm] using this

theorem exists_moved_of_reflection (h2 : (2 : F) ≠ 0) {p r μ : F} (hμ : μ ≠ 0)
    (hpr : p ^ 2 + r ^ 2 = μ) :
    ∃ Y : StatedSp 2 F,
      tens 1 (reflM p r) * mat 2 F Y ≠ mat 2 F Y * tens 1 (reflM p r) ∧
      tens 1 (reflM p r) * mat 2 F Y ≠ -(mat 2 F Y * tens 1 (reflM p r)) := by
  set hm : Matrix (Fin 2) (Fin 2) F := !![1, 0; 0, 2⁻¹] with hhm
  set Nm : Matrix (Fin 2) (Fin 2) F := 1 + Rot with hNm
  have hsymp : (tens hm Nm)ᵀ * gram F 2 * tens hm Nm = gram F 2 := by
    rw [tens_transpose, gram_eq_tens, tens_mul, tens_mul, mul_one]
    have e1 : hmᵀ * J0 * hm = (2⁻¹ : F) • J0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hhm, J0, Matrix.mul_apply, Fin.sum_univ_two]
    have e2 : Nmᵀ * Nm = (2 : F) • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hNm, Rot, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    rw [e1, e2, tens_smul_left, tens_smul_right, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hm00 : hm 0 0 = 1 := by simp [hhm]
  have hmul : tens 1 (reflM p r) * tens hm Nm = tens hm (reflM p r * Nm) := by
    rw [tens_mul, one_mul]
  have hmul' : tens hm Nm * tens 1 (reflM p r) = tens hm (Nm * reflM p r) := by
    rw [tens_mul, mul_one]
  refine ⟨ofSymplecticMat (tens hm Nm) hsymp, ?_, ?_⟩
  · intro hEq
    rw [mat_ofSymplecticMat, hmul, hmul'] at hEq
    have hB := tens_right_injective hm00 hEq
    have e1 := congrFun (congrFun hB 0) 0
    have e2 := congrFun (congrFun hB 0) 1
    simp [reflM, hNm, Rot, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2
    have hr : r = 0 := by
      have : (2 : F) * r = 0 := by linear_combination e1
      exact (mul_eq_zero.mp this).resolve_left h2
    have hp : p = 0 := by
      have : (2 : F) * p = 0 := by linear_combination -e2
      exact (mul_eq_zero.mp this).resolve_left h2
    apply hμ
    rw [← hpr, hr, hp]
    ring
  · intro hEq
    rw [mat_ofSymplecticMat, hmul, hmul', ← tens_neg_right] at hEq
    have hB := tens_right_injective hm00 hEq
    have e1 := congrFun (congrFun hB 0) 0
    have e2 := congrFun (congrFun hB 0) 1
    simp [reflM, hNm, Rot, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2
    have hp : p = 0 := by
      have : (2 : F) * p = 0 := by linear_combination e1
      exact (mul_eq_zero.mp this).resolve_left h2
    have hr : r = 0 := by
      have : (2 : F) * r = 0 := by linear_combination e2
      exact (mul_eq_zero.mp this).resolve_left h2
    apply hμ
    rw [← hpr, hr, hp]
    ring

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
