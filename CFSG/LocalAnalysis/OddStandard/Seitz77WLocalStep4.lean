module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WModule
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.OddStandard.Seitz77

open CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

variable {H : Type} [Group H]

theorem exponent_two (z : H) (hzc : ∀ h, z * h = h * z) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (δ : H →* Multiplicative F4V) (hδ_surj : Function.Surjective δ)
    (hδ_ker : ∀ h, δ h = 1 ↔ (h = 1 ∨ h = z))
    (aU aL : F4 → (H ≃* H))
    (hU : ∀ γ h, δ (aU γ h) = Multiplicative.ofAdd (cUp γ (Multiplicative.toAdd (δ h))))
    (hL : ∀ γ h, δ (aL γ h) = Multiplicative.ofAdd (cLow γ (Multiplicative.toAdd (δ h))))
    (hzU : ∀ γ, aU γ z = z) (hzL : ∀ γ, aL γ z = z) :
    ∀ h : H, h * h = 1 := by
  have hδ2 : ∀ h : H, δ (h * h) = 1 := by
    intro h
    have : Multiplicative.toAdd (δ (h * h)) = 0 := by
      rw [map_mul, toAdd_mul]; exact WFacts.two _
    exact this
  have hsq : ∀ h : H, h * h = 1 ∨ h * h = z := fun h => (hδ_ker _).mp (hδ2 h)
  have hcomm1 : ∀ h k : H, δ ⁅h, k⁆ = 1 := by
    intro h k
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (δ h) (δ k)]
    group
  have hcomm : ∀ h k : H, ⁅h, k⁆ = 1 ∨ ⁅h, k⁆ = z := fun h k => (hδ_ker _).mp (hcomm1 h k)
  have hcent : ∀ h k g : H, ⁅h, k⁆ * g = g * ⁅h, k⁆ := by
    intro h k g
    rcases hcomm h k with h1 | h1
    · rw [h1]; simp
    · rw [h1]; exact hzc g
  have key : ∀ h k : H, (h * k) * (h * k) = ⁅k, h⁆ * ((h * h) * (k * k)) := by
    intro h k
    have e : k * h = ⁅k, h⁆ * (h * k) := by simp only [commutatorElement_def]; group
    calc (h * k) * (h * k) = h * (k * h) * k := by group
      _ = h * (⁅k, h⁆ * (h * k)) * k := by rw [e]
      _ = (h * ⁅k, h⁆) * (h * k) * k := by group
      _ = (⁅k, h⁆ * h) * (h * k) * k := by rw [hcent k h h]
      _ = ⁅k, h⁆ * ((h * h) * (k * k)) := by group
  have hz_mul : ∀ h : H, (h * z) * (h * z) = h * h := by
    intro h
    calc (h * z) * (h * z) = h * (z * h) * z := by group
      _ = h * (h * z) * z := by rw [hzc h]
      _ = h * h * (z * z) := by group
      _ = h * h := by rw [hz2, mul_one]
  have hP_eq : ∀ h h' : H, δ h = δ h' → (h * h = z ↔ h' * h' = z) := by
    intro h h' hh
    have : δ (h⁻¹ * h') = 1 := by rw [map_mul, map_inv, hh]; group
    rcases (hδ_ker _).mp this with h1 | h1
    · have : h' = h := by
        have := congrArg (h * ·) h1
        simpa using this
      rw [this]
    · have : h' = h * z := by
        have := congrArg (h * ·) h1
        simpa using this
      rw [this, hz_mul]
  have hP_aU : ∀ γ h, (aU γ h * aU γ h = z ↔ h * h = z) := by
    intro γ h
    rw [← map_mul]
    constructor
    · intro h1
      apply (aU γ).injective
      rw [h1, hzU γ]
    · intro h1
      rw [h1, hzU γ]
  have hP_aL : ∀ γ h, (aL γ h * aL γ h = z ↔ h * h = z) := by
    intro γ h
    rw [← map_mul]
    constructor
    · intro h1
      apply (aL γ).injective
      rw [h1, hzL γ]
    · intro h1
      rw [h1, hzL γ]
  have hconst : ∀ h h' : H, δ h ≠ 1 → δ h' ≠ 1 → (h * h = z ↔ h' * h' = z) := by
    intro h h' hne hne'
    obtain ⟨a, b, c, e, hw⟩ := WFacts.trans_words (Multiplicative.toAdd (δ h))
      (Multiplicative.toAdd (δ h'))
      (fun h0 => hne (by simpa using h0)) (fun h0 => hne' (by simpa using h0))
    set h'' := aU a (aL b (aU c (aL e h))) with hh''
    have hδ'' : δ h'' = δ h' := by
      rw [hh'', hU, hL, hU, hL]
      simp only [toAdd_ofAdd]
      rw [hw]; simp
    rw [← hP_aL e h, ← hP_aU c, ← hP_aL b, ← hP_aU a]
    exact hP_eq _ _ hδ''
  by_contra hcon
  obtain ⟨h0, h0ne⟩ := not_forall.mp hcon
  have h0z : h0 * h0 = z := (hsq h0).resolve_left h0ne
  have h0δ : δ h0 ≠ 1 := by
    intro h1
    rcases (hδ_ker _).mp h1 with h2 | h2
    · apply h0ne; rw [h2]; simp
    · apply h0ne; rw [h2]; exact hz2
  have hall : ∀ h : H, δ h ≠ 1 → h * h = z := fun h hh => (hconst h0 h h0δ hh).mp h0z
  obtain ⟨x, hx⟩ := hδ_surj (Multiplicative.ofAdd ![(1 : F4), 0])
  obtain ⟨y, hy⟩ := hδ_surj (Multiplicative.ofAdd ![F4.ω, 0])
  obtain ⟨w, hw⟩ := hδ_surj (Multiplicative.ofAdd ![(0 : F4), 1])
  obtain ⟨-, i2, -, i12, -, -, -⟩ := WFacts.three_indep
  have ne1 : ∀ h : H, Multiplicative.toAdd (δ h) ≠ 0 → δ h ≠ 1 :=
    fun h hh h1 => hh (by simp [h1])
  have hx0 : δ x ≠ 1 := ne1 x (by rw [hx]; simp)
  have hy0 : δ y ≠ 1 := ne1 y (by rw [hy]; simpa using i2)
  have hw0 : δ w ≠ 1 := ne1 w (by rw [hw]; simp)
  have hxy0 : δ (x * y) ≠ 1 :=
    ne1 _ (by rw [map_mul δ x y, hx, hy, toAdd_mul]; simpa using i12)
  have hxw0 : δ (x * w) ≠ 1 :=
    ne1 _ (by rw [map_mul δ x w, hx, hw, toAdd_mul]; simp)
  have hyw0 : δ (y * w) ≠ 1 :=
    ne1 _ (by rw [map_mul δ y w, hy, hw, toAdd_mul]; simp)
  have hxyw0 : δ (x * (y * w)) ≠ 1 :=
    ne1 _ (by
      rw [map_mul δ x (y * w), map_mul δ y w, hx, hy, hw, toAdd_mul, toAdd_mul]
      simp)
  have comm_z : ∀ h k : H, δ h ≠ 1 → δ k ≠ 1 → δ (h * k) ≠ 1 → ⁅k, h⁆ = z := by
    intro h k hh hk hhk
    have e := key h k
    rw [hall _ hhk, hall h hh, hall k hk, hz2, mul_one] at e
    simpa using e.symm
  have c1 : ⁅y, x⁆ = z := comm_z x y hx0 hy0 hxy0
  have c2 : ⁅w, x⁆ = z := comm_z x w hx0 hw0 hxw0
  have c3 : ⁅y * w, x⁆ = z := comm_z x (y * w) hx0 hyw0 hxyw0
  have bil : ⁅y * w, x⁆ = ⁅y, x⁆ * ⁅w, x⁆ := by
    calc ⁅y * w, x⁆ = y * ⁅w, x⁆ * (x * y⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
      _ = ⁅w, x⁆ * y * (x * y⁻¹ * x⁻¹) := by rw [hcent w x y]
      _ = ⁅w, x⁆ * ⁅y, x⁆ := by simp only [commutatorElement_def]; group
      _ = ⁅y, x⁆ * ⁅w, x⁆ := (hcent y x ⁅w, x⁆).symm
  rw [bil, c1, c2, hz2] at c3
  exact hz1 c3.symm

end CFSG.OddStandard.Seitz77
