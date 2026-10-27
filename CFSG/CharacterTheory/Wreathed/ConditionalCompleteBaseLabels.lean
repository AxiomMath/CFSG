module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseSetting

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalFiveFixed

variable {ι : Type*} [DecidableEq ι]

theorem pair_label_arith {ε₀ ε₁ d₀ d₁ s τ₀ κ b d : ℤ} (hε₀ : ε₀ = 1 ∨ ε₀ = -1)
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hs : s = 1 ∨ s = -1) (hτ₀ : τ₀ = 1 ∨ τ₀ = -1)
    (hκ : κ = 1 ∨ κ = -1) (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hb : 0 < b) (hd : 0 < d)
    (hsum : ε₀ * d₀ + ε₁ * d₁ = τ₀ * b - κ * d)
    (hdeg : τ₀ * b + κ * d + (s * ε₀ * d₀ - s * ε₁ * d₁) = 0) :
    (s = -1 ∧ ε₀ = τ₀ ∧ d₀ = b ∧ ε₁ = -κ ∧ d₁ = d) ∨
      (s = 1 ∧ ε₁ = τ₀ ∧ d₁ = b ∧ ε₀ = -κ ∧ d₀ = d) := by
  rcases hε₀ with rfl | rfl <;> rcases hε₁ with rfl | rfl <;> rcases hs with rfl | rfl <;>
    rcases hτ₀ with rfl | rfl <;> rcases hκ with rfl | rfl <;> omega

omit [DecidableEq ι] in
theorem two_point_labels {g₀ g₁ : ι} {ε₀ ε₁ s τ₀ κ dB dD K : ℤ} {b x d : ι → ℤ}
    (hε₀ : ε₀ = 1 ∨ ε₀ = -1) (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hs : s = 1 ∨ s = -1)
    (hτ₀ : τ₀ = 1 ∨ τ₀ = -1) (hκ : κ = 1 ∨ κ = -1) (hd₀ : 0 < d g₀) (hd₁ : 0 < d g₁)
    (hdB : 0 < dB) (hdD : 0 < dD) (hb₀ : b g₀ = s * ε₀) (hb₁ : b g₁ = -(s * ε₁))
    (hx₀ : x g₀ = ε₀) (hx₁ : x g₁ = ε₁) (hsum : ε₀ * d g₀ + ε₁ * d g₁ = τ₀ * dB - κ * dD)
    (hK : K = τ₀ * dB + κ * dD) (hdeg : K + (b g₀ * d g₀ + b g₁ * d g₁) = 0) :
    ∃ P Q : ι, ((P = g₀ ∧ Q = g₁) ∨ (P = g₁ ∧ Q = g₀)) ∧ d P = dB ∧ d Q = dD ∧
      x P = τ₀ ∧ x Q = -κ ∧ b P = -τ₀ ∧ b Q = -κ := by
  rw [hb₀, hb₁, hK] at hdeg
  rcases pair_label_arith hε₀ hε₁ hs hτ₀ hκ hd₀ hd₁ hdB hdD hsum (by linarith only [hdeg]) with
    ⟨rfl, h0, h1, h2, h3⟩ | ⟨rfl, h0, h1, h2, h3⟩
  · refine ⟨g₀, g₁, Or.inl ⟨rfl, rfl⟩, h1, h3, by rw [hx₀, h0], by rw [hx₁, h2],
      by rw [hb₀, h0]; ring, by rw [hb₁, h2]; ring⟩
  · refine ⟨g₁, g₀, Or.inr ⟨rfl, rfl⟩, h1, h3, by rw [hx₁, h0], by rw [hx₀, h2],
      by rw [hb₁, h0]; ring, by rw [hb₀, h2]; ring⟩


variable {B : Finset ι} {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ} {κ' : Type*} {J : Finset κ'}
  {χ : κ' → ι} {y₀ C : ι → ℤ} {xj : κ' → ι → ℤ} {M : ℕ}
  {γ : ℕ → Fin 4 → ι} {ε : ℕ → Fin 4 → ℤ} {xk yr : ℕ → ι → ℤ} {cd cd' : ℕ → ι → ℤ}
  {β : Type*} {V : Finset β} {dg : β → ι → ℤ}

@[expose] def baseFixed (p A ω : ι) (σ τ₀ : ℤ) : ι → ℤ := fun φ =>
  unitVector p φ - σ * unitVector A φ + 2 * τ₀ * unitVector ω φ

theorem diag_rep (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) {γ' : Fin 4 → ι}
    {ε' : Fin 4 → ℤ} {xk' yr' : ι → ℤ} (hQ : Quadruple B p A Bq Dq ω σ τ₀ κ J χ γ' ε' xk' yr')
    {b : ι → ℤ} (hb1 : b p = 1) (hbA : b A = -σ) (hbB : b Bq = 0) (hbD : b Dq = 0)
    (hbω : b ω = 2 * τ₀) (hbχ : ∀ j ∈ J, b (χ j) = 0)
    (hb0 : ∀ φ ∈ B, Outside p A Bq Dq ω J χ γ' φ → b φ = 0) {P Q : ι} (hPQ : P ≠ Q)
    (hPγ : ∃ l, P = γ' l) (hQγ : ∃ l, Q = γ' l) (hbP : b P = -τ₀) (hbQ : b Q = -κ)
    (hother : ∀ l, γ' l ≠ P → γ' l ≠ Q → b (γ' l) = 0) :
    ∀ φ ∈ B, b φ = baseFixed p A ω σ τ₀ φ - τ₀ * unitVector P φ - κ * unitVector Q φ := by
  obtain ⟨lP, rfl⟩ := hPγ
  obtain ⟨lQ, rfl⟩ := hQγ
  have hcP := hQ.core lP
  have hcQ := hQ.core lQ
  intro φ hφ
  simp only [baseFixed, unitVector]
  by_cases h1 : φ = p
  · subst h1
    simp [hb1, hS.hAp.symm, hS.hωp.symm, hcP.1.symm, hcQ.1.symm]
  by_cases h2 : φ = A
  · subst h2
    simp [hbA, hS.hAp, hS.hωA.symm, hcP.2.1.symm, hcQ.2.1.symm]
  by_cases h3 : φ = ω
  · subst h3
    simp [hbω, hS.hωp, hS.hωA, hcP.2.2.2.2.symm, hcQ.2.2.2.2.symm]
  by_cases h4 : φ = γ' lP
  · subst h4
    simp [hbP, hcP.1, hcP.2.1, hcP.2.2.2.2, hPQ]
  by_cases h5 : φ = γ' lQ
  · subst h5
    simp [hbQ, hcQ.1, hcQ.2.1, hcQ.2.2.2.2, hPQ.symm]
  simp only [h1, h2, h3, h4, h5, ite_false, mul_zero, sub_zero]
  by_cases h6 : φ = Bq
  · subst h6
    simp [hbB]
  by_cases h7 : φ = Dq
  · subst h7
    simp [hbD]
  by_cases h8 : ∃ j ∈ J, φ = χ j
  · obtain ⟨j, hj, rfl⟩ := h8
    simp [hbχ j hj]
  by_cases h9 : ∃ l, φ = γ' l
  · obtain ⟨l, rfl⟩ := h9
    rw [hother l (fun h => h4 h) (fun h => h5 h)]
    ring
  push Not at h8 h9
  rw [hb0 φ hφ ⟨h1, h2, h6, h7, h3, h8, h9⟩]
  ring

end CFSG.Wreathed.ConditionalCompleteBase
