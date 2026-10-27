module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.WeakClosure
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ElimFacts

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

theorem false_of_goldschmidt (hG : Goldschmidt74Cor4) {G : Type} [Group G] [Finite G]
    {C R : Subgroup G} (hCab : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c) (hC2 : ∀ c ∈ C, c * c = 1)
    (hCR : C ≤ R) (hR2 : IsPGroup 2 R) (hRN : R ≤ normalizer (C : Set G))
    (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ normalizer (C : Set G) → R ≤ Q → Q ≤ R)
    (hweak : ∀ D : Subgroup G, D ≤ R → (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) →
      (∀ x ∈ D, x * x = 1) → ¬ D ≤ C → Nat.card D = Nat.card C →
      ∃ d ∈ D, d ∉ C ∧ C.relIndex D < (centralizer ({d} : Set G)).relIndex C)
    (hrank : ∀ B : Subgroup G, B ≤ R → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → (centralizer (C : Set G)).relIndex B ≤ 16)
    (t : G) (htR : t ∈ R) (htC : t ∉ C) (ht2 : orderOf t = 2) (htconj : ∃ g : G, g * t * g⁻¹ ∈ C)
    (hcomm : 16 < Nat.card (⁅C, zpowers t⁆ : Subgroup G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwc := weaklyClosed_of_relIndex_lt hCab hC2 hweak
  obtain ⟨T, hTR⟩ := exists_sylow_eq_of_weaklyClosed hR2 hRN hmax hwc hCR
  have hwcT : ∀ g : G, C.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      C.map (MulAut.conj g).toMonoidHom = C := by
    rw [hTR]
    exact hwc
  obtain ⟨g, hg⟩ := htconj
  have e : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t := by group
  obtain ⟨ρ, ⟨B, hB, hBρ⟩, -, -, hII⟩ := hG G T C (hTR ▸ hCR) hCab hC2 hwcT
    ⟨g * t * g⁻¹, hg, g⁻¹, by rw [hTR, e]; exact htR, by rw [e]; exact htC⟩
  obtain ⟨hBT, hBC, g', hg'⟩ := hB
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have hxy := hCab _ (hg' ⟨x, hx, rfl⟩) _ (hg' ⟨y, hy, rfl⟩)
    have : g' * (x * y) * g'⁻¹ = g' * (y * x) * g'⁻¹ := by
      calc g' * (x * y) * g'⁻¹ = (g' * x * g'⁻¹) * (g' * y * g'⁻¹) := by group
        _ = (g' * y * g'⁻¹) * (g' * x * g'⁻¹) := hxy
        _ = g' * (y * x) * g'⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)
  have hB2 : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    have h1 := hC2 _ (hg' ⟨x, hx, rfl⟩)
    have : g' * (x * x) * g'⁻¹ = 1 := by
      calc g' * (x * x) * g'⁻¹ = (g' * x * g'⁻¹) * (g' * x * g'⁻¹) := by group
        _ = 1 := h1
    simpa using this
  have hρ : ρ ≤ 16 := hBρ ▸ hrank B (hTR ▸ hBT) hBab hB2
  have hle := hII t (hTR ▸ htR) ht2 ⟨g, hg⟩
  omega

end CFSG.EvenSporadicStandard.M24Std
