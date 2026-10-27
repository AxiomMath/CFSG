module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallTwoForm
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSplitArith

public section

namespace CFSG.SeitzReduction.RankOne

section PencilNF

variable {E : Type*} [Field E]

theorem pencilNF_exists_sigma_ne [Finite E] {σ : E →+* E} {q : ℕ} (hq : 2 ≤ q)
    (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q) : ∃ β : E, σ β ≠ β := by
  by_contra hall
  push Not at hall
  have h1 : Nat.card {x : E // σ x = x} = Nat.card E :=
    Nat.card_congr (Equiv.subtypeUnivEquiv hall)
  rw [hF, hE] at h1
  have : q < q ^ 2 := by nlinarith
  omega

theorem pencilNF_coeff_eq [CharP E 2] {σ : E →+* E} {β₀ : E} (hβ₀ : σ β₀ ≠ β₀)
    {A A' B B' : E}
    (h : ∀ α β : E, A * (α * σ β) + A' * (σ α * β) = B * (α * σ β) + B' * (σ α * β)) :
    A = B ∧ A' = B' := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have h11 := h 1 1
  have h1b := h 1 β₀
  simp only [map_one, one_mul, mul_one] at h11 h1b
  have hne : σ β₀ + β₀ ≠ 0 := by
    intro h0
    apply hβ₀
    linear_combination h0 - β₀ * h2
  have hc : (A - B) * (σ β₀ + β₀) = 0 := by
    linear_combination h1b - β₀ * h11 + (A - B) * β₀ * h2
  have hAB : A - B = 0 := (mul_eq_zero.mp hc).resolve_right hne
  refine ⟨sub_eq_zero.mp hAB, ?_⟩
  linear_combination h11 - hAB

theorem pencilNF_sum_sq_add_sum [CharP E 2] (x : E) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ 2 ^ i) ^ 2 + ∑ i ∈ Finset.range n, x ^ 2 ^ i = x ^ 2 ^ n + x := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, pow_one]
    linear_combination -x * h2
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ 2 n, pow_mul]
    linear_combination ih + (∑ i ∈ Finset.range n, x ^ 2 ^ i) * x ^ 2 ^ n * h2 +
      x ^ 2 ^ n * h2

theorem pencilNF_exists_sq_add_self_eq [CharP E 2] {σ : E →+* E} {f : ℕ}
    (hσ : ∀ x, σ x = x ^ 2 ^ f) (hσσ : ∀ x, σ (σ x) = x) {β₀ : E} (hβ₀ : σ β₀ ≠ β₀) {δ : E}
    (hδ : σ δ = δ) : ∃ z : E, z ^ 2 + z = δ := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hne : β₀ + σ β₀ ≠ 0 := by
    intro h0
    apply hβ₀
    linear_combination h0 - β₀ * h2
  set x := δ * β₀ / (β₀ + σ β₀) with hx
  have hσx : σ x = δ * σ β₀ / (β₀ + σ β₀) := by
    rw [hx, map_div₀, map_mul, map_add, hδ, hσσ, add_comm (σ β₀) β₀]
  have htr : x ^ 2 ^ f + x = δ := by
    rw [← hσ, hσx, hx, ← add_div, ← mul_add, add_comm (σ β₀) β₀,
      mul_div_assoc, div_self hne, mul_one]
  exact ⟨∑ i ∈ Finset.range f, x ^ 2 ^ i, by rw [pencilNF_sum_sq_add_sum, htr]⟩

theorem pencilNF_eq_zero_of_additive_weight [Fintype E] {f : ℕ} (hf : 2 ≤ f)
    (hK : Fintype.card E = (2 ^ f) ^ 2) (ℓ : E → E) (hℓ : ∀ x y, ℓ (x + y) = ℓ x + ℓ y)
    {μ : E} (hμ0 : μ ≠ 0) (hμ : orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1))
    (hℓμ : ∀ x, ℓ (μ * x) = μ ^ (2 ^ f + 1) * ℓ x) (x : E) : ℓ x = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Fintype.card E = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hcard : Nat.card E = 2 ^ (2 * f) := by rw [Nat.card_eq_fintype_card, hK']
  obtain ⟨hb, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases Nat.prime_two
      (n := 2 * f) (by omega) hcard
  let g : E →+ E := AddMonoidHom.mk' ℓ hℓ
  obtain ⟨c, hc, -⟩ := hb g
  have hc' : ∀ u, ℓ u = ∑ i, c i * u ^ 2 ^ (i : ℕ) := hc
  have hlt : 2 ^ (2 * f - 1) < Fintype.card E := by
    rw [hK']
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hcoef : ∀ i : Fin (2 * f), c i * μ ^ 2 ^ (i : ℕ) = c i * μ ^ (2 ^ f + 1) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.eq_zero_of_forall_sum_mul_pow_eq_zero hlt
      (a := fun i => c i * μ ^ 2 ^ (i : ℕ) - c i * μ ^ (2 ^ f + 1)) fun u => by
        have h1 := hℓμ u
        rw [hc' (μ * u), hc' u, Finset.mul_sum] at h1
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        calc ∑ i, c i * μ ^ 2 ^ (i : ℕ) * u ^ 2 ^ (i : ℕ) = ∑ i, c i * (μ * u) ^ 2 ^ (i : ℕ) :=
              Finset.sum_congr rfl fun i _ => by rw [mul_pow]; ring
          _ = ∑ i, μ ^ (2 ^ f + 1) * (c i * u ^ 2 ^ (i : ℕ)) := h1
          _ = _ := Finset.sum_congr rfl fun i _ => by ring
    intro i
    exact sub_eq_zero.mp (congrFun h i)
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hzero : ∀ i : Fin (2 * f), c i = 0 := by
    intro i
    by_contra hci
    have h1 : μ ^ 2 ^ (i : ℕ) = μ ^ (2 ^ f + 1) := mul_left_cancel₀ hci (hcoef i)
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
    ·
      rw [hi0, pow_zero, pow_one, pow_succ] at h1
      have hq1 : μ ^ 2 ^ f = 1 := mul_right_cancel₀ hμ0 (h1.symm.trans (one_mul μ).symm)
      have hμ1 : μ = 1 := by
        have h3 : μ ^ Fintype.card E = μ := FiniteField.pow_card μ
        rw [hK, sq, pow_mul, hq1, one_pow] at h3
        exact h3.symm
      have ho : orderOf μ = 1 := by rw [hμ1, orderOf_one]
      rw [hμ] at ho
      have hg : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
      have hgpos : 0 < Nat.gcd 3 (2 ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
      have hsq : 4 ^ 2 ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hq4 2
      have h2le : 2 ≤ ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) := by
        rw [Nat.le_div_iff_mul_le hgpos]
        generalize (2 ^ f) ^ 2 = Q at hsq ⊢
        generalize Nat.gcd 3 (2 ^ f + 1) = m at hg ⊢
        omega
      omega
    ·
      obtain ⟨j, hj⟩ : ∃ j, (i : ℕ) = j + 1 := ⟨(i : ℕ) - 1, by omega⟩
      have hjlt : j < 2 * f := by have := i.2; omega
      have h1' : μ ^ (2 ^ j + 2 ^ j) = μ ^ (2 ^ f + 1) := by
        rw [← two_mul, ← pow_succ', ← hj]
        exact h1
      have key := eq_zero_f_of_dvd_two_pow_add_two_pow hf hjlt hjlt hμ ?_ ?_
      · rcases key with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
      · rcases Nat.lt_or_ge (2 ^ j + 2 ^ j) (2 ^ f + 1) with hlt' | hge
        · rw [Nat.sub_eq_zero_of_le hlt'.le]
          exact dvd_zero _
        · apply orderOf_dvd_of_pow_eq_one
          have e : μ ^ (2 ^ j + 2 ^ j) =
              μ ^ (2 ^ j + 2 ^ j - (2 ^ f + 1)) * μ ^ (2 ^ f + 1) := by
            rw [← pow_add, Nat.sub_add_cancel hge]
          rw [e] at h1'
          exact mul_right_cancel₀ (pow_ne_zero _ hμ0) (h1'.trans (one_mul _).symm)
      · rcases Nat.lt_or_ge (2 ^ f + 1) (2 ^ j + 2 ^ j) with hlt' | hge
        · rw [Nat.sub_eq_zero_of_le hlt'.le]
          exact dvd_zero _
        · apply orderOf_dvd_of_pow_eq_one
          have e : μ ^ (2 ^ f + 1) =
              μ ^ (2 ^ f + 1 - (2 ^ j + 2 ^ j)) * μ ^ (2 ^ j + 2 ^ j) := by
            rw [← pow_add, Nat.sub_add_cancel hge]
          rw [e] at h1'
          exact mul_right_cancel₀ (pow_ne_zero _ hμ0) (h1'.symm.trans (one_mul _).symm)
  rw [hc' x]
  exact Finset.sum_eq_zero fun i _ => by rw [hzero i, zero_mul]

theorem pencilNF_normalForm [CharP E 2] {σ : E →+* E} (hσσ : ∀ x, σ (σ x) = x) {β₀ : E}
    (hβ₀ : σ β₀ ≠ β₀)
    {γ₀₀ γ₀₀' γ₀₁ γ₀₁' γ₁₀ γ₁₀' γ₁₁ γ₁₁' ε₀₀ ε₀₀' ε₀₁ ε₀₁' ε₁₀ ε₁₀' ε₁₁ ε₁₁' : E}
    (P₁ P₂ : E → E → E → E → E)
    (hP₁ : ∀ X₀ X₁ Y₀ Y₁, P₁ X₀ X₁ Y₀ Y₁ =
      (γ₀₀ * (X₀ * σ Y₀) + γ₀₀' * (σ X₀ * Y₀)) + (γ₀₁ * (X₀ * σ Y₁) + γ₀₁' * (σ X₀ * Y₁)) +
        (γ₁₀ * (X₁ * σ Y₀) + γ₁₀' * (σ X₁ * Y₀)) + (γ₁₁ * (X₁ * σ Y₁) + γ₁₁' * (σ X₁ * Y₁)))
    (hP₂ : ∀ X₀ X₁ Y₀ Y₁, P₂ X₀ X₁ Y₀ Y₁ =
      (ε₀₀ * (X₀ * σ Y₀) + ε₀₀' * (σ X₀ * Y₀)) + (ε₀₁ * (X₀ * σ Y₁) + ε₀₁' * (σ X₀ * Y₁)) +
        (ε₁₀ * (X₁ * σ Y₀) + ε₁₀' * (σ X₁ * Y₀)) + (ε₁₁ * (X₁ * σ Y₁) + ε₁₁' * (σ X₁ * Y₁)))
    (hfix₁ : ∀ X₀ X₁ Y₀ Y₁, σ (P₁ X₀ X₁ Y₀ Y₁) = P₁ X₀ X₁ Y₀ Y₁)
    (hfix₂ : ∀ X₀ X₁ Y₀ Y₁, σ (P₂ X₀ X₁ Y₀ Y₁) = P₂ X₀ X₁ Y₀ Y₁)
    (halt₂ : ∀ X₀ X₁, P₂ X₀ X₁ X₀ X₁ = 0)
    (ht₁ : ∀ X₀ X₁ Y₀ Y₁, P₁ (X₀ + X₁) X₁ (Y₀ + Y₁) Y₁ = P₁ X₀ X₁ Y₀ Y₁)
    (ht₂ : ∀ X₀ X₁ Y₀ Y₁,
      P₂ (X₀ + X₁) X₁ (Y₀ + Y₁) Y₁ = P₁ X₀ X₁ Y₀ Y₁ + P₂ X₀ X₁ Y₀ Y₁)
    (hT₁ : ∀ X₀ Y₀, P₁ X₀ 0 Y₀ 0 = 0) (hT₂ : ∀ X₀ Y₀, P₂ X₀ 0 Y₀ 0 = TraceForm.form σ X₀ Y₀) :
    ∃ g δ : E, σ δ = δ ∧ ∀ X₀ X₁ Y₀ Y₁,
      P₁ X₀ X₁ Y₀ Y₁ = TraceForm.form σ (X₀ + σ g * X₁) Y₁ +
        TraceForm.form σ X₁ (Y₀ + σ g * Y₁) + TraceForm.form σ X₁ Y₁ ∧
      P₂ X₀ X₁ Y₀ Y₁ = TraceForm.form σ (X₀ + σ g * X₁) (Y₀ + σ g * Y₁) +
        δ * TraceForm.form σ X₁ Y₁ := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have herm : ∀ c c' : E, (∀ α β : E, σ (c * (α * σ β) + c' * (σ α * β)) =
      c * (α * σ β) + c' * (σ α * β)) → c' = σ c := by
    intro c c' h
    refine (pencilNF_coeff_eq hβ₀ (A := σ c') (A' := σ c) (B := c) (B' := c')
      fun α β => ?_).2.symm
    have e := h α β
    simp only [map_add, map_mul, hσσ] at e
    linear_combination e
  have e00 := herm γ₀₀ γ₀₀' fun α β => by
    have h := hfix₁ α 0 β 0
    simp only [hP₁, map_zero, mul_zero, zero_mul, add_zero] at h
    exact h
  have e01 := herm γ₀₁ γ₀₁' fun α β => by
    have h := hfix₁ α 0 0 β
    simp only [hP₁, map_zero, mul_zero, zero_mul, add_zero, zero_add] at h
    exact h
  have e10 := herm γ₁₀ γ₁₀' fun α β => by
    have h := hfix₁ 0 α β 0
    simp only [hP₁, map_zero, mul_zero, zero_mul, add_zero, zero_add] at h
    exact h
  have e11 := herm γ₁₁ γ₁₁' fun α β => by
    have h := hfix₁ 0 α 0 β
    simp only [hP₁, map_zero, mul_zero, zero_mul, add_zero, zero_add] at h
    exact h
  have f00 := herm ε₀₀ ε₀₀' fun α β => by
    have h := hfix₂ α 0 β 0
    simp only [hP₂, map_zero, mul_zero, zero_mul, add_zero] at h
    exact h
  have f01 := herm ε₀₁ ε₀₁' fun α β => by
    have h := hfix₂ α 0 0 β
    simp only [hP₂, map_zero, mul_zero, zero_mul, add_zero, zero_add] at h
    exact h
  have f10 := herm ε₁₀ ε₁₀' fun α β => by
    have h := hfix₂ 0 α β 0
    simp only [hP₂, map_zero, mul_zero, zero_mul, add_zero, zero_add] at h
    exact h
  have f11 := herm ε₁₁ ε₁₁' fun α β => by
    have h := hfix₂ 0 α 0 β
    simp only [hP₂, map_zero, mul_zero, zero_mul, add_zero, zero_add] at h
    exact h
  subst e00 e01 e10 e11 f00 f01 f10 f11
  have hγ₀₀ : γ₀₀ = 0 := (pencilNF_coeff_eq hβ₀ (A := γ₀₀) (A' := σ γ₀₀) (B := 0) (B' := 0)
    fun α β => by
      have h := hT₁ α β
      simp only [hP₁, map_zero, mul_zero, zero_mul, add_zero] at h
      linear_combination h).1
  have hε₀₀ : ε₀₀ = 1 := (pencilNF_coeff_eq hβ₀ (A := ε₀₀) (A' := σ ε₀₀) (B := 1) (B' := 1)
    fun α β => by
      have h := hT₂ α β
      simp only [hP₂, TraceForm.form, map_zero, mul_zero, zero_mul, add_zero] at h
      linear_combination h).1
  subst hγ₀₀ hε₀₀
  have hγ₀₁ : γ₀₁ = 1 := by
    have := (pencilNF_coeff_eq hβ₀ (A := 1 + ε₀₁) (A' := 1 + σ ε₀₁) (B := γ₀₁ + ε₀₁)
      (B' := σ γ₀₁ + σ ε₀₁) fun α β => by
        have h := ht₂ α 0 0 β
        simp only [hP₁, hP₂, map_zero, map_one, mul_zero, zero_mul, add_zero, zero_add] at h
        linear_combination h).1
    linear_combination -this
  subst hγ₀₁
  have hγ₁₀ : γ₁₀ = 1 := by
    have := (pencilNF_coeff_eq hβ₀ (A := 1 + γ₁₀ + γ₁₁) (A' := 1 + σ γ₁₀ + σ γ₁₁) (B := γ₁₁)
      (B' := σ γ₁₁) fun α β => by
        have h := ht₁ 0 α 0 β
        simp only [hP₁, map_zero, map_one, mul_zero, zero_mul, add_zero, zero_add] at h
        linear_combination h).1
    linear_combination this - h2
  subst hγ₁₀
  have h11 : ε₁₁ + σ ε₁₁ = 0 := by
    have h := halt₂ 0 1
    simp only [hP₂, map_zero, map_one, mul_zero, add_zero, zero_add, mul_one] at h
    linear_combination h
  have hε₁₀ : ε₁₀ = σ ε₀₁ := by
    have := (pencilNF_coeff_eq hβ₀ (A := ε₀₁ + σ ε₁₀) (A' := σ ε₀₁ + ε₁₀) (B := 0) (B' := 0)
      fun α β => by
        have h := halt₂ α β
        simp only [hP₂, map_one] at h
        linear_combination h - α * σ α * h2 - β * σ β * h11).2
    linear_combination this - σ ε₀₁ * h2
  subst hε₁₀
  have hγ₁₁ : γ₁₁ = 1 + ε₀₁ + σ ε₀₁ := by
    have := (pencilNF_coeff_eq hβ₀ (A := 1 + ε₀₁ + σ ε₀₁ + ε₁₁)
      (A' := 1 + σ ε₀₁ + ε₀₁ + σ ε₁₁) (B := γ₁₁ + ε₁₁) (B' := σ γ₁₁ + σ ε₁₁) fun α β => by
        have h := ht₂ 0 α 0 β
        simp only [hP₁, hP₂, map_zero, map_one, mul_zero, zero_mul, add_zero, zero_add,
          hσσ] at h
        linear_combination h).1
    linear_combination -this
  subst hγ₁₁
  have hc : σ ε₁₁ = ε₁₁ := by linear_combination h11 - ε₁₁ * h2
  refine ⟨ε₀₁, ε₁₁ - ε₀₁ * σ ε₀₁, ?_, fun X₀ X₁ Y₀ Y₁ => ⟨?_, ?_⟩⟩
  · rw [map_sub, map_mul, hσσ, hc]
    ring
  · rw [hP₁]
    simp only [TraceForm.form, map_add, map_mul, hσσ, map_one, map_zero]
    ring
  · rw [hP₂]
    simp only [TraceForm.form, map_add, map_mul, hσσ, map_one, hc]
    ring

end PencilNF

end CFSG.SeitzReduction.RankOne
