module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteWStar
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJField

set_option linter.unusedSectionVars false

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.ClassicalInvolution.G2D4Models
  CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.SEITZ3

@[expose] def Phi6Placement {K : Type} [Field K] (σ : K →+* K)
    (hσ : ∀ c, σ (σ (σ c)) = c) (q : ℕ) (E₀ : Subgroup (twistedGroup σ))
    (w : twistedGroup σ) : Prop :=
  ∃ (g : twistedGroup σ) (D : Subgroup (twistedGroup σ)) (x₁ c a b : twistedGroup σ),
    g * w * g⁻¹ = slLong σ hσ (-1) ∧ IsSimpleGroup D ∧ ⁅D, D⁆ = D ∧
    Nat.card D = q * (q ^ 2 - 1) / 2 ∧ (∀ x ∈ D, x * w = w * x) ∧
    x₁ ∈ E₀ ∧ x₁ ≠ 1 ∧ (∀ x ∈ D, x * x₁ = x₁ * x) ∧
    (∀ x ∈ D, g * x * g⁻¹ ∈ JTw σ) ∧ c ∈ E₀ ∧ c ≠ 1 ∧ g * c * g⁻¹ ∈ JTw σ ∧
    (∀ x ∈ E₀, a * x * a⁻¹ ∈ E₀) ∧ (∀ x ∈ E₀, b * x * b⁻¹ ∈ E₀) ∧
    g * a * g⁻¹ ∈ invCentGroup σ hσ ∧ g * b * g⁻¹ ∈ invCentGroup σ hσ ∧
    a * b * a⁻¹ * b⁻¹ = w

@[expose] def Phi6CoreWGe5 (r : ℕ) : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → 5 ≤ ℓ ^ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c,
    r.Prime → r ≠ ℓ → (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 →
    ∃ (E₀ : Subgroup (twistedGroup σ.toRingHom)) (w : twistedGroup σ.toRingHom)
      (P : Sylow r (twistedGroup σ.toRingHom)),
      (∀ x ∈ E₀, x ^ r = 1) ∧ Nat.card E₀ = r ^ 2 ∧ w * w = 1 ∧
      (∀ x ∈ E₀, w * x * w⁻¹ = x⁻¹) ∧ E₀ ≤ (P : Subgroup (twistedGroup σ.toRingHom)) ∧
      (∀ x ∈ (P : Subgroup (twistedGroup σ.toRingHom)),
        ∀ y ∈ (P : Subgroup (twistedGroup σ.toRingHom)), x * y = y * x) ∧
      (∀ x ∈ (P : Subgroup (twistedGroup σ.toRingHom)), x ^ r = 1 → x ∈ E₀) ∧
      (∃ g : twistedGroup σ.toRingHom, g * w * g⁻¹ = slLong σ.toRingHom hσ (-1) ∧
        (invCentGroup σ.toRingHom hσ).map (MulAut.conj g⁻¹).toMonoidHom ≤ closure (cenGen E₀)) ∧
      (∃ u x₁ : twistedGroup σ.toRingHom, u * u = 1 ∧ u ≠ 1 ∧ x₁ ∈ E₀ ∧ x₁ ≠ 1 ∧
        u * w = w * u ∧ u * x₁ = x₁ * u)

theorem conj_mem_closure_cenGen {G : Type*} [Group G] {E : Subgroup G} {ν : G}
    (hν : ∀ x ∈ E, ν * x * ν⁻¹ ∈ E) {y : G} (hy : y ∈ closure (cenGen E)) :
    ν * y * ν⁻¹ ∈ closure (cenGen E) := by
  have h1 : (closure (cenGen E)).map (MulAut.conj ν).toMonoidHom ≤ closure (cenGen E) := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨k, ⟨x, hx, hx1, hk⟩, rfl⟩
    refine subset_closure ⟨ν * x * ν⁻¹, hν x hx, ?_, ?_⟩
    · intro h
      exact hx1 (mul_left_cancel ((mul_inv_eq_one.1 h).trans (mul_one ν).symm))
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc ν * k * ν⁻¹ * (ν * x * ν⁻¹) = ν * (k * x) * ν⁻¹ := by group
        _ = ν * (x * k) * ν⁻¹ := by rw [hk]
        _ = ν * x * ν⁻¹ * (ν * k * ν⁻¹) := by group
  exact h1 ⟨y, hy, rfl⟩

@[expose] def Phi6CoreWLt5 (r : ℕ) : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ℓ ^ f < 5 → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c,
    r.Prime → r ≠ ℓ → (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 →
    ∃ (E₀ : Subgroup (twistedGroup σ.toRingHom)) (w : twistedGroup σ.toRingHom)
      (P : Sylow r (twistedGroup σ.toRingHom)),
      (∀ x ∈ E₀, x ^ r = 1) ∧ Nat.card E₀ = r ^ 2 ∧ w * w = 1 ∧
      (∀ x ∈ E₀, w * x * w⁻¹ = x⁻¹) ∧ E₀ ≤ (P : Subgroup (twistedGroup σ.toRingHom)) ∧
      (∀ x ∈ (P : Subgroup (twistedGroup σ.toRingHom)),
        ∀ y ∈ (P : Subgroup (twistedGroup σ.toRingHom)), x * y = y * x) ∧
      (∀ x ∈ (P : Subgroup (twistedGroup σ.toRingHom)), x ^ r = 1 → x ∈ E₀) ∧
      (∃ g : twistedGroup σ.toRingHom, g * w * g⁻¹ = slLong σ.toRingHom hσ (-1) ∧
        (invCentGroup σ.toRingHom hσ).map (MulAut.conj g⁻¹).toMonoidHom ≤ closure (cenGen E₀)) ∧
      (∃ u x₁ : twistedGroup σ.toRingHom, u * u = 1 ∧ u ≠ 1 ∧ x₁ ∈ E₀ ∧ x₁ ≠ 1 ∧
        u * w = w * u ∧ u * x₁ = x₁ * u)

theorem phi6CoreW_of_ge5_of_lt5 {r : ℕ} (h5 : Phi6CoreWGe5 r) (h3 : Phi6CoreWLt5 r) :
    Phi6CoreW r := by
  intro ℓ f hℓ hℓ2 hf K _ _ hK σ hσq hσ hr hrℓ hd
  by_cases hq : 5 ≤ ℓ ^ f
  · exact h5 ℓ f hℓ hℓ2 hf hq K hK σ hσq hσ hr hrℓ hd
  · exact h3 ℓ f hℓ hℓ2 hf (by omega) K hK σ hσq hσ hr hrℓ hd

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
