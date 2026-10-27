module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46T

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_sq_eq_of_moves {Z : Subgroup G} (hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    (h4 : Nat.card ↥(omegaOne Z) ≤ 4) (hZ4 : ∀ z ∈ Z, z ^ 4 = 1) {e : G} (heZ : e ∈ Z)
    (hee : e * e ≠ 1) {a b : G} (haZ : a ∈ Z) (haa : a * a = 1) (ha1 : a ≠ 1)
    (hba : b * a = a * b) (hbZ : ∀ z ∈ Z, b * z * b⁻¹ ∈ Z) (hbb : b * b = 1) {f : G}
    (hfZ : f ∈ Z) (hff : f * f = 1) (hbf : b * f * b⁻¹ ≠ f) :
    ∃ z ∈ Z, z * b = b * z ∧ z * z = a := by
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  set β : G → G := fun x => b * x * b⁻¹ with hβ
  have hβmul : ∀ x y, β (x * y) = β x * β y := fun x y => by simp only [hβ]; group
  have hββ : ∀ x, β (β x) = x := fun x => by
    simp only [hβ]
    rw [hbi, show b * (b * x * b) * b = (b * b) * x * (b * b) by group, hbb]
    group
  have hβa : β a = a := by
    simp only [hβ]
    rw [hba, mul_inv_cancel_right]
  have hfix : ∀ x, β x = x → x * b = b * x := fun x hx => by
    simp only [hβ] at hx
    calc x * b = b * x * b⁻¹ * b := by rw [hx]
      _ = b * x := by group
  have hsq : ∀ x, β x * β x = 1 ↔ x * x = 1 := fun x => by
    rw [← hβmul]
    simp only [hβ]
    constructor
    · intro h
      calc x * x = b⁻¹ * (b * (x * x) * b⁻¹) * b := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  have hβ1 : ∀ x, β x = 1 ↔ x = 1 := fun x => by
    simp only [hβ]
    constructor
    · intro h
      calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  have hβZ : ∀ x ∈ Z, β x ∈ Z := hbZ
  have hf1 : f ≠ 1 := fun h => hbf (by rw [h]; group)
  have hfa : f ≠ a := fun h => hbf (by rw [h]; exact hβa)
  have hbf1 : β f ≠ 1 := fun h => hf1 ((hβ1 f).mp h)
  have hbfa : β f ≠ a := fun h => hfa (by rw [← hββ f, h, hβa])
  have hbff : β f * β f = 1 := (hsq f).mpr hff
  have hbfaf : β f = a * f := by
    have h := eq_mul_of_card_omegaOne_le_four h4 haZ hfZ (hβZ f hfZ) haa hff hbff ha1 hf1 hbf1
      hfa.symm hbfa.symm (Ne.symm hbf)
    exact h
  have haf : a * f ∈ Z := mul_mem haZ hfZ
  have hafaf : a * f * (a * f) = 1 := by
    rw [show a * f * (a * f) = a * a * (f * f) by
      rw [mul_assoc a f, ← mul_assoc f a, ← hZab a haZ f hfZ]; group, haa, hff, one_mul]
  have hβaf : β (a * f) = f := by
    rw [hβmul, hβa, hbfaf, ← mul_assoc, haa, one_mul]
  have hinvs : ∀ x ∈ Z, x * x = 1 → x = 1 ∨ x = a ∨ x = f ∨ x = a * f := by
    intro x hxZ hxx
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨hx1, hxa, hxf, hxaf⟩ := hne
    exact hxaf (eq_mul_of_card_omegaOne_le_four h4 haZ hfZ hxZ haa hff hxx ha1 hf1 hx1 hfa.symm
      (Ne.symm hxa) (Ne.symm hxf))
  have he2Z : e * e ∈ Z := mul_mem heZ heZ
  have he4 : e * e * (e * e) = 1 := by
    have h := hZ4 e heZ
    rw [show (4 : ℕ) = 1 + 1 + 1 + 1 by norm_num, pow_add, pow_add, pow_add, pow_one] at h
    rw [← h]
    group
  have hβe : β e ∈ Z := hβZ e heZ
  have hcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := hZab
  rcases hinvs (e * e) he2Z he4 with h | h | h | h
  · exact absurd h hee
  ·
    set N := e * β e with hN
    have hNZ : N ∈ Z := mul_mem heZ hβe
    have hβN : β N = N := by
      rw [hN, hβmul, hββ, hcomm (β e) hβe e heZ]
    have hNN : N * N = 1 := by
      have hβe2 : β e * β e = a := by rw [← hβmul, h, hβa]
      calc N * N = e * e * (β e * β e) := by
            rw [hN, mul_assoc e (β e), ← mul_assoc (β e) e, ← hcomm e heZ (β e) hβe]; group
        _ = 1 := by rw [h, hβe2, haa]
    rcases hinvs N hNZ hNN with hN1 | hNa | hNf | hNaf
    ·
      have hβei : β e = e⁻¹ := by
        rw [hN] at hN1
        exact eq_inv_of_mul_eq_one_right hN1
      refine ⟨e * f, mul_mem heZ hfZ, hfix _ ?_, ?_⟩
      · rw [hβmul, hβei, hbfaf, ← h]
        group
      · calc e * f * (e * f) = e * e * (f * f) := by
              rw [mul_assoc e f, ← mul_assoc f e, ← hcomm e heZ f hfZ]; group
          _ = a := by rw [h, hff, mul_one]
    ·
      have hβee : β e = e := by
        rw [hN] at hNa
        calc β e = e⁻¹ * (e * β e) := by group
          _ = e⁻¹ * a := by rw [hNa]
          _ = e := by rw [← h]; group
      exact ⟨e, heZ, hfix e hβee, h⟩
    · exfalso
      have h1 : β f = f := by rw [← hNf]; exact hβN
      exact hbf h1
    · exfalso
      have h1 : β (a * f) = a * f := by rw [← hNaf]; exact hβN
      rw [hβaf] at h1
      apply ha1
      calc a = a * f * f := by rw [mul_assoc, hff, mul_one]
        _ = f * f := by rw [← h1]
        _ = 1 := hff
  ·
    refine ⟨e * β e, mul_mem heZ hβe, hfix _ ?_, ?_⟩
    · rw [hβmul, hββ, hcomm (β e) hβe e heZ]
    · calc e * β e * (e * β e) = e * e * (β e * β e) := by
            rw [mul_assoc e (β e), ← mul_assoc (β e) e, ← hcomm e heZ (β e) hβe]; group
        _ = f * (a * f) := by rw [h, ← hβmul, h, hbfaf]
        _ = a := by rw [← mul_assoc, hcomm f hfZ a haZ, mul_assoc, hff, mul_one]
  ·
    refine ⟨e * β e, mul_mem heZ hβe, hfix _ ?_, ?_⟩
    · rw [hβmul, hββ, hcomm (β e) hβe e heZ]
    · calc e * β e * (e * β e) = e * e * (β e * β e) := by
            rw [mul_assoc e (β e), ← mul_assoc (β e) e, ← hcomm e heZ (β e) hβe]; group
        _ = a * f * f := by rw [h, ← hβmul, h, hβaf]
        _ = a := by rw [mul_assoc, hff, mul_one]

end CFSG.ComponentClassification.GrSLit.GrS4
