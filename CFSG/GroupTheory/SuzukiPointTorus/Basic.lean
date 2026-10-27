module

public import Mathlib.GroupTheory.Frattini

public section

namespace CFSG.GroupTheory

universe u
variable {X : Type u} [Group X] [Finite X]

structure SuzukiTorusData (X : Type*) [Group X] [Finite X] (q : ℕ) : Prop where
  faithful : FaithfulSMul X (Sylow 2 X)
  card_points : Nat.card (Sylow 2 X) = q ^ 2 + 1
  fixes_le_two : ∀ g : X, g ≠ 1 → Nat.card {P : Sylow 2 X // g • P = P} ≤ 2
  card_sylow : ∀ U : Sylow 2 X, Nat.card U = q ^ 2
  regular : ∀ U V W : Sylow 2 X, V ≠ U → W ≠ U →
    ∃! u : U, (u : X) • V = W
  inf_normalizer_isCyclic : ∀ U U' : Sylow 2 X, U ≠ U' → IsCyclic
    ↥(Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
      Subgroup.normalizer ((U' : Subgroup X) : Set X))
  inf_normalizer_card : ∀ U U' : Sylow 2 X, U ≠ U' →
    Nat.card ↥(Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
      Subgroup.normalizer ((U' : Subgroup X) : Set X)) = q - 1
  inf_normalizer_free : ∀ (U U' : Sylow 2 X), U ≠ U' →
    ∀ h ∈ Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
        Subgroup.normalizer ((U' : Subgroup X) : Set X),
      h ≠ 1 → ∀ u : U, (h : X) * (u : X) * (h : X)⁻¹ = (u : X) → u = 1
  card_frattini : ∀ U : Sylow 2 X, Nat.card (↥U ⧸ frattini ↥U) = q

namespace SuzukiTorusData

variable {q : ℕ} (h : SuzukiTorusData X q)

@[expose] def torus (U₁ U₂ : Sylow 2 X) : Subgroup X :=
  Subgroup.normalizer ((U₁ : Subgroup X) : Set X) ⊓
    Subgroup.normalizer ((U₂ : Subgroup X) : Set X)

theorem torus_le_normalizer_left {U₁ U₂ : Sylow 2 X} :
    torus U₁ U₂ ≤ Subgroup.normalizer ((U₁ : Subgroup X) : Set X) :=
  inf_le_left

theorem torus_le_normalizer_right {U₁ U₂ : Sylow 2 X} :
    torus U₁ U₂ ≤ Subgroup.normalizer ((U₂ : Subgroup X) : Set X) :=
  inf_le_right

theorem torus_isCyclic (h : SuzukiTorusData X q) {U₁ U₂ : Sylow 2 X} (hne : U₁ ≠ U₂) :
    IsCyclic (torus U₁ U₂) :=
  SuzukiTorusData.inf_normalizer_isCyclic h U₁ U₂ hne

theorem torus_card (h : SuzukiTorusData X q) {U₁ U₂ : Sylow 2 X} (hne : U₁ ≠ U₂) :
    Nat.card (torus U₁ U₂) = q - 1 :=
  SuzukiTorusData.inf_normalizer_card h U₁ U₂ hne

theorem sylow_finite : Finite (Sylow 2 X) :=
  Finite.of_injective (fun P : Sylow 2 X => (P : Subgroup X))
    (fun P Q h => Sylow.ext h)

end SuzukiTorusData

end CFSG.GroupTheory
