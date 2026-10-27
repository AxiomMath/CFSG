module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabL
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OutL
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag Blocks

variable {F : Type} [Field F] [Fintype F]

omit [Fintype F] in
theorem conjAut_mul_fieldAut_pow (B : GL (Fin 4) F) (τ : F ≃+* F) (n : ℕ) :
    ∃ C : GL (Fin 4) F,
      (conjAut 4 F B * fieldAut 4 F τ) ^ n = conjAut 4 F C * fieldAut 4 F (τ ^ n) := by
  induction n with
  | zero => exact ⟨1, by rw [pow_zero, pow_zero, map_one, map_one, one_mul]⟩
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * GeneralLinearGroup.map ((τ ^ n : F ≃+* F) : F →+* F) B, ?_⟩
    rw [pow_succ, hC, conjAut_mul_fieldAut_mul, pow_succ]

omit [Fintype F] in
theorem sq_eq_conjAut_mul_fieldAut (A : GL (Fin 4) F) (σ : F ≃+* F) {ε : ℕ} (hε : ε ≤ 1) :
    ∃ B : GL (Fin 4) F, (conjAut 4 F A * fieldAut 4 F σ * dualAut 4 F ^ ε) ^ 2 =
      conjAut 4 F B * fieldAut 4 F (σ ^ 2) := by
  have htrans := standard_automorphism_transport (K := F) (n := 4)
  interval_cases ε
  · refine ⟨A * GeneralLinearGroup.map (σ : F →+* F) A, ?_⟩
    rw [pow_zero, mul_one, sq, conjAut_mul_fieldAut_mul, sq]
  · refine ⟨A * GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.inverseTranspose A), ?_⟩
    have h : dualAut 4 F * (conjAut 4 F A * fieldAut 4 F σ) * dualAut 4 F =
        conjAut 4 F (GeneralLinearGroup.inverseTranspose A) * fieldAut 4 F σ := by
      calc dualAut 4 F * (conjAut 4 F A * fieldAut 4 F σ) * dualAut 4 F
          = dualAut 4 F * conjAut 4 F A * (dualAut 4 F * dualAut 4 F) * fieldAut 4 F σ *
              dualAut 4 F := by rw [htrans.2.2.2.1]; group
        _ = (dualAut 4 F * conjAut 4 F A * dualAut 4 F) *
              (dualAut 4 F * fieldAut 4 F σ * dualAut 4 F) := by group
        _ = _ := by rw [htrans.2.2.2.2.1, htrans.2.2.2.2.2.1]
    rw [pow_one, sq, sq, ← conjAut_mul_fieldAut_mul, ← h]
    calc conjAut 4 F A * fieldAut 4 F σ * dualAut 4 F * (conjAut 4 F A * fieldAut 4 F σ *
          dualAut 4 F)
        = conjAut 4 F A * fieldAut 4 F σ * (dualAut 4 F * (conjAut 4 F A * fieldAut 4 F σ) *
            dualAut 4 F) := by group

theorem fieldAut_eq_one_of_pow {p f : ℕ} (hp : p.Prime) (hK : Nat.card F = p ^ f) (hf : Odd f)
    (A : GL (Fin 4) F) (σ : F ≃+* F) {ε : ℕ} (hε : ε ≤ 1) {m : ℕ}
    (hα : (conjAut 4 F A * fieldAut 4 F σ * dualAut 4 F ^ ε) ^ (2 ^ (m + 1)) = 1) : σ = 1 := by
  obtain ⟨B, hB⟩ := sq_eq_conjAut_mul_fieldAut A σ hε
  obtain ⟨C, hC⟩ := conjAut_mul_fieldAut_pow B (σ ^ 2) (2 ^ m)
  rw [pow_succ', pow_mul, hB, hC] at hα
  have h1 := (eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) C _ hα).1
  rw [← pow_mul, ← pow_succ'] at h1
  have h2 : σ ^ f = 1 := by
    rw [← (card_ringAut_and_isCyclic hp F hK).1]
    exact pow_card_eq_one'
  have hcop : Nat.gcd (2 ^ (m + 1)) f = 1 :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hf)
  have := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [hcop, pow_one] at this

omit [Fintype F] in
theorem det_smul_add_smul (a b : F) :
    (a • 1 + b • stdJ : Matrix (Fin 4) (Fin 4) F).det = (a ^ 2 + b ^ 2) ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [stdJ, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove,
    Matrix.one_apply]
  ring

theorem isSquare_or_isSquare_neg (hns : ¬ IsSquare (-1 : F)) {x : F} (hx : x ≠ 0) :
    IsSquare x ∨ IsSquare (-x) := by
  classical
  by_cases h : IsSquare x
  · exact Or.inl h
  · right
    have h2 : ringChar F ≠ 2 := by
      intro h2
      exact hns (FiniteField.isSquare_of_char_two h2 (-1))
    have hx1 := (quadraticChar_neg_one_iff_not_isSquare).2 h
    have hm1 := (quadraticChar_neg_one_iff_not_isSquare).2 hns
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.2 hx), neg_eq_neg_one_mul,
      map_mul, hx1, hm1]
    norm_num

theorem comm_of_conjAut_fix (hF : Fintype.card F % 4 = 3) (A : GL (Fin 4) F)
    {u : SpecialLinearGroup (Fin 4) F} (hu : (u : Matrix (Fin 4) (Fin 4) F).trace = 4)
    (h : conjAut 4 F A (proj 4 F u) = proj 4 F u) :
    (A : Matrix (Fin 4) (Fin 4) F) * u = u * A := by
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have hc : ringChar F = 2 := by
      have := (ringChar.spec F 2).1 (by exact_mod_cast h0)
      exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F (ringChar F)) Nat.prime_two).1 this
    have := FiniteField.even_card_iff_char_two.1 hc
    omega
  rw [conjAut_proj] at h
  have hc := coe_slConjugation A u
  have h3 := eq_of_eq_or_neg_of_trace h2 (eq_of_proj_eq hF h.symm) (by
    rw [hc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]) hu
  rw [hc] at h3
  calc (A : Matrix (Fin 4) (Fin 4) F) * u = A * u * ((A⁻¹ : GL (Fin 4) F) * A) := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    _ = u * A := by rw [← Matrix.mul_assoc, h3]

theorem invariant_of_conjAut_dual_fix (hF : Fintype.card F % 4 = 3) (A : GL (Fin 4) F)
    {u : SpecialLinearGroup (Fin 4) F} (hu : (u : Matrix (Fin 4) (Fin 4) F).trace = 4)
    (hu' : ((u⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).trace = 4)
    (h : (conjAut 4 F A * dualAut 4 F) (proj 4 F u) = proj 4 F u) :
    (u : Matrix (Fin 4) (Fin 4) F) * A * (u : Matrix (Fin 4) (Fin 4) F)ᵀ = A := by
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have hc : ringChar F = 2 := by
      have := (ringChar.spec F 2).1 (by exact_mod_cast h0)
      exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F (ringChar F)) Nat.prime_two).1 this
    have := FiniteField.even_card_iff_char_two.1 hc
    omega
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj] at h
  have hc := coe_slConjugation A ((u⁻¹).transpose)
  have h3 := eq_of_eq_or_neg_of_trace h2 (eq_of_proj_eq hF h.symm) (by
    rw [hc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.trace_transpose, hu', hu]) hu
  rw [hc, Matrix.SpecialLinearGroup.coe_transpose] at h3
  have hui : ((u⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * u = 1 :=
    congrArg (fun y : SpecialLinearGroup (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F))
      (inv_mul_cancel u)
  calc (u : Matrix (Fin 4) (Fin 4) F) * A * (u : Matrix (Fin 4) (Fin 4) F)ᵀ
      = (A * ((u⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * A *
            (u : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [h3]
    _ = A * (((u : Matrix (Fin 4) (Fin 4) F)) * ((u⁻¹ : SpecialLinearGroup (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F))ᵀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F),
          ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    _ = A := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one]

omit [Field F] in
theorem odd_of_card_mod_four (hF : Fintype.card F % 4 = 3) {p f : ℕ}
    (hK : Nat.card F = p ^ f) : Odd f := by
  rcases Nat.even_or_odd f with ⟨t, rfl⟩ | h
  · exfalso
    rw [Nat.card_eq_fintype_card] at hK
    rw [hK, ← two_mul, pow_mul, Nat.pow_mod] at hF
    have h4 : (p ^ 2 % 4) < 4 := Nat.mod_lt _ (by norm_num)
    have hsq : p ^ 2 % 4 = 0 ∨ p ^ 2 % 4 = 1 := by
      rw [Nat.pow_mod]
      have : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
      interval_cases p % 4 <;> simp
    rcases hsq with h0 | h1
    · rw [h0] at hF
      rcases t with _ | t
      · simp at hF
      · rw [zero_pow (by omega)] at hF
        simp at hF
    · rw [h1, one_pow] at hF
      simp at hF
  · exact h

theorem inner_or_alternating (hF : Fintype.card F % 4 = 3) {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card F = p ^ f) (α : MulAut (projectiveSL 4 F)) {m : ℕ}
    (hα2 : α ^ (2 ^ (m + 1)) = 1) {J' : Subgroup (projectiveSL 4 F)} (hJ' : HasUnipotents J')
    (hfix : ∀ x ∈ J', α x = x) :
    α ∈ (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)).range ∨
      ∃ A : GL (Fin 4) F, (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A ∧
        α = conjAut 4 F A * dualAut 4 F := by
  have hns : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
  have hσ := fieldAut_eq_one_of_pow hp hK (odd_of_card_mod_four hF hK) A σ hε hα2
  subst hσ
  simp only [map_one, mul_one] at hfix ⊢
  obtain ⟨h1, h2, h3⟩ := hJ'
  interval_cases ε
  · left
    simp only [pow_zero, mul_one] at hfix ⊢
    have hc : ∀ u : SpecialLinearGroup (Fin 4) F, (u : Matrix (Fin 4) (Fin 4) F).trace = 4 →
        proj 4 F u ∈ J' → (A : Matrix (Fin 4) (Fin 4) F) * u = u * A :=
      fun u hu hmem => comm_of_conjAut_fix hF A hu (hfix _ hmem)
    have hA := eq_of_comm_unipotents (hc (slA 1 0) (trace_uA 1 0) h1)
      (hc (slA 0 1) (trace_uA 0 1) h2) (hc (slB 1 0) (trace_uB 1 0) h3)
    set a := (A : Matrix (Fin 4) (Fin 4) F) 0 0
    set b := (A : Matrix (Fin 4) (Fin 4) F) 1 0
    have hdet : ((GeneralLinearGroup.det A : Fˣ) : F) = (a ^ 2 + b ^ 2) ^ 2 := by
      rw [GeneralLinearGroup.val_det_apply, hA, det_smul_add_smul]
    have hx : a ^ 2 + b ^ 2 ≠ 0 := by
      intro h0
      have := (GeneralLinearGroup.det A).ne_zero
      rw [hdet, h0] at this
      exact this (by ring)
    obtain ⟨r, hr⟩ : ∃ r : F, r ^ 4 = (a ^ 2 + b ^ 2) ^ 2 := by
      rcases isSquare_or_isSquare_neg hns hx with ⟨r, hr⟩ | ⟨r, hr⟩
      · exact ⟨r, by rw [hr]; ring⟩
      · refine ⟨r, ?_⟩
        have : a ^ 2 + b ^ 2 = -(r * r) := by linear_combination -hr
        rw [this]
        ring
    have hr0 : r ≠ 0 := by
      rintro rfl
      apply hx
      have : (a ^ 2 + b ^ 2) ^ 2 = 0 := by rw [← hr]; ring
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    exact LinearOut.conjAut_mem_range_of_det A (Units.mk0 r hr0) (Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hr, hdet]))
  · right
    simp only [pow_one] at hfix ⊢
    refine ⟨A, ?_, rfl⟩
    have hc : ∀ u : SpecialLinearGroup (Fin 4) F, (u : Matrix (Fin 4) (Fin 4) F).trace = 4 →
        ((u⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).trace = 4 →
        proj 4 F u ∈ J' →
        (u : Matrix (Fin 4) (Fin 4) F) * A * (u : Matrix (Fin 4) (Fin 4) F)ᵀ = A :=
      fun u hu hu' hmem => invariant_of_conjAut_dual_fix hF A hu hu' (hfix _ hmem)
    exact transpose_eq_neg_of_unipotents
      (hc (slA 1 0) (trace_uA 1 0) (by rw [coe_slA_inv]; exact trace_uA _ _) h1)
      (hc (slA 0 1) (trace_uA 0 1) (by rw [coe_slA_inv]; exact trace_uA _ _) h2)
      (hc (slB 1 0) (trace_uB 1 0) (by rw [coe_slB_inv]; exact trace_uB _ _) h3)

theorem inner_or_fixed_not_mem_normalizer (hF : Fintype.card F % 4 = 3) {p f : ℕ}
    (hp : p.Prime) (hK : Nat.card F = p ^ f) (α : MulAut (projectiveSL 4 F)) {m : ℕ}
    (hα2 : α ^ (2 ^ (m + 1)) = 1) {J' : Subgroup (projectiveSL 4 F)}
    (hJk : J' ≤ Subgroup.centralizer {proj 4 F k₀}) (hJ' : HasUnipotents J')
    (hfix : ∀ x ∈ J', α x = x) :
    α ∈ (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)).range ∨
      ∃ x : projectiveSL 4 F, α x = x ∧ x ∉ Subgroup.normalizer (J' : Set (projectiveSL 4 F)) := by
  rcases inner_or_alternating hF hp hK α hα2 hJ' hfix with h | ⟨A, hA, rfl⟩
  · exact Or.inl h
  · right
    have h2 := two_ne_zero_of_card_mod_four hF
    have hAu : IsUnit (A : Matrix (Fin 4) (Fin 4) F).det := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.isUnit _
    obtain ⟨h, hdet, hAh, hne1, hne2⟩ := exists_transvection h2 hA hAu
    set hS : SpecialLinearGroup (Fin 4) F := ⟨h, hdet⟩ with hSdef
    have hhu : IsUnit h.det := by rw [hdet]; exact isUnit_one
    have hinv : ((hS⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = h⁻¹ :=
      coe_inv_eq (Matrix.mul_nonsing_inv _ hhu)
    have hAA : (A : Matrix (Fin 4) (Fin 4) F) * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨proj 4 F hS, ?_, ?_⟩
    · rw [MulAut.mul_apply, dualAut_proj, conjAut_proj]
      congr 1
      apply Subtype.ext
      rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose, hinv,
        Matrix.transpose_nonsing_inv]
      have hTu : IsUnit hᵀ.det := by rw [Matrix.det_transpose]; exact hhu
      calc (A : Matrix (Fin 4) (Fin 4) F) * hᵀ⁻¹ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
          = h * A * hᵀ * hᵀ⁻¹ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by rw [hAh]
        _ = h * (A * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc hᵀ, Matrix.mul_nonsing_inv _ hTu, Matrix.one_mul]
        _ = h := by rw [hAA, Matrix.mul_one]
    · intro hN
      have hconj : ((hS * k₀ * hS⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          h * stdJ * h⁻¹ := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv]
        rfl
      have hhi : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul _ hhu
      rcases conj_k₀_eq_or_neg hF hJk hJ' hN with h1 | h1
      · apply hne1
        rw [hconj] at h1
        calc h * stdJ = h * stdJ * h⁻¹ * h := by rw [Matrix.mul_assoc _ h⁻¹, hhi, Matrix.mul_one]
          _ = stdJ * h := by rw [h1]
      · apply hne2
        rw [hconj] at h1
        calc h * stdJ = h * stdJ * h⁻¹ * h := by rw [Matrix.mul_assoc _ h⁻¹, hhi, Matrix.mul_one]
          _ = -(stdJ * h) := by rw [h1, Matrix.neg_mul]

end StabL

end CFSG.ComponentClassification.CatFactsL4U4
