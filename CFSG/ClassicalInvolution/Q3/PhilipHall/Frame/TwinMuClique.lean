module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonClass

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu

open CFSG.ClassicalInvolution.Asc77.Star3T

variable {Q : Type*} [Group Q] {Δ : Set Q}

theorem exists_fourth (h : IsTT Δ) (hS : IsStar Δ) {d a : Q} (hd : d ∈ Δ) (ha : a ∈ Δ)
    (hc : ¬ Conn Δ d a) {x₁ x₂ x₃ : Q} (h₁ : x₁ ∈ cent Δ d) (h₂ : x₂ ∈ cent Δ d)
    (h₃ : x₃ ∈ cent Δ d) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    ∃ x₄ ∈ cent Δ d, x₄ ≠ x₁ ∧ x₄ ≠ x₂ ∧ x₄ ≠ x₃ ∧
      a * x₄ * a = (x₁ * x₂ * x₃) * a * (x₃ * x₂ * x₁) := by
  have hpl := isPlane_of_not_conn hd ha hc
  have hcl : ∀ u ∈ cent Δ d, ∀ v ∈ cent Δ d, u * v = v * u := fun u hu v hv =>
    h.isClique_cent hS hd ha hc hu hv
  have hbr : ∀ x ∈ cent Δ d, x * a * x = a * x * a := fun x hx =>
    h.braid hx.1 ha (noncomm_of_mem_cent hpl hx)
  have hz : x₁ * (x₂ * (x₃ * a * x₃) * x₂) * x₁ ∈ cent Δ (d * a * d) := by
    have hpl' : IsPlane Δ d (d * a * d) a := h.isPlane_rot hpl
    have u3 : x₃ * a * x₃ ∈ cent Δ (d * a * d) :=
      h.cent_conj_mem hS hpl h₃ (self_mem_cent ha)
    have u2 : x₂ * (x₃ * a * x₃) * x₂ ∈ cent Δ a := h.cent_conj_mem hS hpl' h₂ u3
    exact h.cent_conj_mem hS hpl h₁ u2
  have himg := h.cent_eq_image hS (h.isPlane_swap hpl)
  rw [himg] at hz
  obtain ⟨x₄, h₄, hx₄⟩ := hz
  have hx₄' : a * x₄ * a = (x₁ * x₂ * x₃) * a * (x₃ * x₂ * x₁) := by
    have := hx₄
    simp only at this
    rw [this]
    simp only [mul_assoc]
  have c12 : x₁ * x₂ = x₂ * x₁ := hcl _ h₁ _ h₂
  have c13 : x₁ * x₃ = x₃ * x₁ := hcl _ h₁ _ h₃
  have c23 : x₂ * x₃ = x₃ * x₂ := hcl _ h₂ _ h₃
  refine ⟨x₄, h₄, ?_, ?_, ?_, hx₄'⟩
  · intro e
    rw [e] at hx₄'
    exact h23 (eq_of_conj_eq h h₁.1 h₂.1 h₃.1 (hbr _ h₁) (hbr _ h₂) (hbr _ h₃) hx₄')
  · intro e
    rw [e] at hx₄'
    have e1 : x₁ * x₂ * x₃ = x₂ * x₁ * x₃ := by rw [c12]
    have e2 : x₃ * x₂ * x₁ = x₃ * x₁ * x₂ := by
      calc x₃ * x₂ * x₁ = x₃ * (x₂ * x₁) := mul_assoc _ _ _
        _ = x₃ * (x₁ * x₂) := by rw [← c12]
        _ = x₃ * x₁ * x₂ := (mul_assoc _ _ _).symm
    rw [e1, e2] at hx₄'
    exact h13 (eq_of_conj_eq h h₂.1 h₁.1 h₃.1 (hbr _ h₂) (hbr _ h₁) (hbr _ h₃) hx₄')
  · intro e
    rw [e] at hx₄'
    have e1 : x₁ * x₂ * x₃ = x₃ * x₁ * x₂ := by
      calc x₁ * x₂ * x₃ = x₁ * (x₂ * x₃) := mul_assoc _ _ _
        _ = x₁ * (x₃ * x₂) := by rw [c23]
        _ = x₁ * x₃ * x₂ := (mul_assoc _ _ _).symm
        _ = x₃ * x₁ * x₂ := by rw [c13]
    have e2 : x₃ * x₂ * x₁ = x₂ * x₁ * x₃ := by
      calc x₃ * x₂ * x₁ = x₂ * x₃ * x₁ := by rw [← c23]
        _ = x₂ * (x₃ * x₁) := mul_assoc _ _ _
        _ = x₂ * (x₁ * x₃) := by rw [← c13]
        _ = x₂ * x₁ * x₃ := (mul_assoc _ _ _).symm
    rw [e1, e2] at hx₄'
    exact h12 (eq_of_conj_eq h h₃.1 h₁.1 h₂.1 (hbr _ h₃) (hbr _ h₁) (hbr _ h₂) hx₄')

theorem prod_comm {a x₁ x₂ x₃ x₄ : Q} (ha : a * a = 1) (h1 : x₁ * x₁ = 1) (h2 : x₂ * x₂ = 1)
    (h3 : x₃ * x₃ = 1) (h4 : x₄ * x₄ = 1) (c12 : x₁ * x₂ = x₂ * x₁) (c13 : x₁ * x₃ = x₃ * x₁)
    (c23 : x₂ * x₃ = x₃ * x₂) (c14 : x₁ * x₄ = x₄ * x₁) (c24 : x₂ * x₄ = x₄ * x₂)
    (c34 : x₃ * x₄ = x₄ * x₃) (hx₄ : a * x₄ * a = (x₁ * x₂ * x₃) * a * (x₃ * x₂ * x₁)) :
    (x₁ * x₂ * x₃ * x₄) * a = a * (x₁ * x₂ * x₃ * x₄) := by
  set P := x₁ * x₂ * x₃ with hP
  have hP12 : Commute x₁ x₂ := c12
  have hP13 : Commute x₁ x₃ := c13
  have hP23 : Commute x₂ x₃ := c23
  have hPP : P * P = 1 := by
    have e1 : (x₁ * x₂ * x₃) * (x₁ * x₂ * x₃) = (x₁ * x₂) * (x₁ * x₂) * (x₃ * x₃) := by
      have : Commute x₃ (x₁ * x₂) := (hP13.symm.mul_right hP23.symm)
      calc (x₁ * x₂ * x₃) * (x₁ * x₂ * x₃) = (x₁ * x₂) * (x₃ * (x₁ * x₂)) * x₃ := by
            simp only [mul_assoc]
        _ = (x₁ * x₂) * ((x₁ * x₂) * x₃) * x₃ := by rw [this.eq]
        _ = (x₁ * x₂) * (x₁ * x₂) * (x₃ * x₃) := by simp only [mul_assoc]
    have e2 : (x₁ * x₂) * (x₁ * x₂) = (x₁ * x₁) * (x₂ * x₂) := by
      calc (x₁ * x₂) * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by simp only [mul_assoc]
        _ = x₁ * (x₁ * x₂) * x₂ := by rw [← c12]
        _ = (x₁ * x₁) * (x₂ * x₂) := by simp only [mul_assoc]
    rw [hP, e1, e2, h1, h2, h3]; simp
  have hPinv : x₃ * x₂ * x₁ = P := by
    have : x₃ * x₂ * x₁ = x₁ * x₂ * x₃ := by
      calc x₃ * x₂ * x₁ = x₃ * (x₂ * x₁) := mul_assoc _ _ _
        _ = x₃ * (x₁ * x₂) := by rw [← c12]
        _ = x₃ * x₁ * x₂ := (mul_assoc _ _ _).symm
        _ = x₁ * x₃ * x₂ := by rw [← c13]
        _ = x₁ * (x₃ * x₂) := mul_assoc _ _ _
        _ = x₁ * (x₂ * x₃) := by rw [← c23]
        _ = x₁ * x₂ * x₃ := (mul_assoc _ _ _).symm
    rw [this]
  rw [hPinv] at hx₄
  have hPx4 : P * x₄ = x₄ * P := by
    have : Commute (x₁ * x₂ * x₃) x₄ := ((Commute.mul_left (Commute.mul_left (c14 : Commute x₁ x₄)
      (c24 : Commute x₂ x₄)) (c34 : Commute x₃ x₄)))
    exact this.eq
  have hx4' : x₄ = a * P * a * P * a := by
    calc x₄ = (a * a) * x₄ * (a * a) := by rw [ha]; simp
      _ = a * (a * x₄ * a) * a := by simp only [mul_assoc]
      _ = a * (P * a * P) * a := by rw [hx₄]
      _ = a * P * a * P * a := by simp only [mul_assoc]
  have hc : P * x₄ = (P * a) * (P * a) * (P * a) := by
    calc P * x₄ = P * (a * P * a * P * a) := by rw [← hx4']
      _ = (P * a) * (P * a) * (P * a) := by simp only [mul_assoc]
  have hcc : (P * x₄) * (P * x₄) = 1 := by
    calc (P * x₄) * (P * x₄) = P * (x₄ * P) * x₄ := by simp only [mul_assoc]
      _ = P * (P * x₄) * x₄ := by rw [hPx4]
      _ = (P * P) * (x₄ * x₄) := by simp only [mul_assoc]
      _ = 1 := by rw [hPP, h4]; simp
  have hacom : a * (P * x₄) * a = (a * P) * (a * P) * (a * P) := by
    rw [hc]
    calc a * ((P * a) * (P * a) * (P * a)) * a = (a * P) * (a * P) * (a * P) * (a * a) := by
          simp only [mul_assoc]
      _ = (a * P) * (a * P) * (a * P) := by rw [ha]; simp
  have hinv : (a * P) * (P * a) = 1 := by
    calc (a * P) * (P * a) = a * (P * P) * a := by simp only [mul_assoc]
      _ = 1 := by rw [hPP]; simpa using ha
  have key : ∀ A B : Q, A * B = 1 → A * A * A * (B * B * B) = 1 := by
    intro A B hAB
    calc A * A * A * (B * B * B) = A * A * (A * B) * B * B := by simp only [mul_assoc]
      _ = A * A * B * B := by rw [hAB, mul_one]
      _ = A * (A * B) * B := by simp only [mul_assoc]
      _ = 1 := by rw [hAB, mul_one]; exact hAB
  have hinv' : (a * P) * (a * P) * (a * P) * ((P * a) * (P * a) * (P * a)) = 1 :=
    key _ _ hinv
  have h5 : a * (P * x₄) * a = (P * x₄) := by
    rw [hacom]
    have h6 : (a * P) * (a * P) * (a * P) = (P * x₄)⁻¹ := by
      rw [hc]
      exact eq_inv_of_mul_eq_one_left hinv'
    rw [h6]
    exact inv_eq_of_mul_eq_one_right hcc
  have h7 : a * (P * x₄) = (P * x₄) * a := by
    calc a * (P * x₄) = a * (P * x₄) * (a * a) := by rw [ha]; simp
      _ = (a * (P * x₄) * a) * a := by simp only [mul_assoc]
      _ = (P * x₄) * a := by rw [h5]
  have hfin : x₁ * x₂ * x₃ * x₄ = P * x₄ := rfl
  rw [hfin]
  exact h7.symm

theorem conj_swap (h : IsTT Δ) {d s : Q} (hd : d ∈ Δ) (hs : s ∈ Δ) (hc : ¬ Conn Δ d s) :
    (d * s) * d * (d * s)⁻¹ = s := by
  have hnc : d * s ≠ s * d := fun e => hc (conn_of_commute hd hs e)
  have hb := h.braid hd hs hnc
  have hdd := h.mul_self d hd
  have hss := h.mul_self s hs
  have e : (d * s) * d * (d * s)⁻¹ = d * s * d * s * d := by
    rw [mul_inv_rev, h.inv_eq hd, h.inv_eq hs]
    simp only [mul_assoc]
  rw [e]
  calc d * s * d * s * d = (d * s * d) * s * d := by simp only [mul_assoc]
    _ = (s * d * s) * s * d := by rw [hb]
    _ = s * d * (s * s) * d := by simp only [mul_assoc]
    _ = s := by rw [hss]; simp only [mul_one, mul_assoc, hdd]

theorem conj_cent {c d s : Q} (hcd : c * d = d * c) (hcs : c * s = s * c) :
    (d * s) * c * (d * s)⁻¹ = c := by
  have e : (d * s) * c = c * (d * s) := by
    calc (d * s) * c = d * (s * c) := mul_assoc _ _ _
      _ = d * (c * s) := by rw [← hcs]
      _ = (d * c) * s := (mul_assoc _ _ _).symm
      _ = (c * d) * s := by rw [← hcd]
      _ = c * (d * s) := mul_assoc _ _ _
  rw [e]; group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu
