module

public import CFSG.ClassicalInvolution.Asc77.WP1Defs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def L7_1 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      (∀ J ∈ Ω, AEmpty Ω J) →
        ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ u r v t : G,
          Subgroup.zpowers u = R ⊓ W → R = Subgroup.closure {u, r} →
          Subgroup.zpowers v = T ⊓ W → T = Subgroup.closure {v, t} →
            (R ⊔ T ⊔ OCW W) ⊓ W = Subgroup.closure {u, v} ∧
            ((∃ J ∈ Ω, R ≤ J ∧ T ≤ J) ∨
              (∃ J ∈ Ω, ∃ J' ∈ Ω, R ≤ J ∧ T ≤ J' ∧ J' ∈ omegaNbr Ω J ∧
                ∀ a ∈ R, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ OCW W) ∨
              (∃ J ∈ Ω, ∃ J' ∈ Ω, R ≤ J ∧ T ≤ J' ∧ J' ∈ omegaStarNbr Ω J ∧
                J' ∉ omegaNbr Ω J ∧
                ∃ v' : G, Subgroup.zpowers v' = Subgroup.zpowers v ∧
                  t⁻¹ * u * t * (u * v')⁻¹ ∈ OCW W ∧ r⁻¹ * v' * r * (v' * u)⁻¹ ∈ OCW W))

@[expose] def L7_5_2 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ W ∈ WSet Ω, ∀ W' ∈ WSet Ω, Nonempty (↥(muGroup Ω W) ≃* ↥(muGroup Ω W'))

@[expose] def L7_9 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      (∀ J ∈ Ω, AEmpty Ω J) →
        ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ S ∈ DSet Ω W,
          DComm W R T → DOrder3 W R S → DOrder3 W T S →
            ∀ u r v t w s : G,
              Subgroup.zpowers u = R ⊓ W → R = Subgroup.closure {u, r} →
              Subgroup.zpowers v = T ⊓ W → T = Subgroup.closure {v, t} →
              Subgroup.zpowers w = S ⊓ W → S = Subgroup.closure {w, s} →
                (R ⊔ S ⊔ T) ⊓ OCW W = ⊥ →
                  (∃ v' w' : G, Subgroup.zpowers v' = Subgroup.zpowers v ∧
                    Subgroup.zpowers w' = Subgroup.zpowers w ∧
                    r⁻¹ * w' * r = w' * u ∧ w' * u = s⁻¹ * u * s ∧
                    t⁻¹ * w' * t = w' * v' ∧ w' * v' = s⁻¹ * v' * s) ∧
                  ∃ φ : ↥(R ⊔ S ⊔ T) →* Equiv.Perm (Fin 4), Function.Surjective φ ∧
                    φ.ker = ((R ⊔ S ⊔ T) ⊓ (W ⊔ OCW W)).subgroupOf (R ⊔ S ⊔ T)

@[expose] def L7_14 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      (∀ J ∈ Ω, AEmpty Ω J) →
        ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, DOrder3 W R T →
          ∀ L U : Subgroup G, L = R ⊔ T → U = L ⊓ W → oddCoreOf L = ⊥ →
            ∀ x : G, IsPGroup 2 (Subgroup.zpowers x) → conjSub x L = L →
              (∀ y ∈ U, y * y = 1 → x * y = y * x) →
                (∀ u v : G, Subgroup.zpowers u = R ⊓ W → Subgroup.zpowers v = T ⊓ W →
                  ∀ k : ℤ, (∃ i : ℕ, x ^ i * u * (x ^ i)⁻¹ = u ^ k) ↔
                    (∃ i : ℕ, x ^ i * v * (x ^ i)⁻¹ = v ^ k)) ∧
                ((∀ y ∈ U, x * y = y * x) →
                  Subgroup.zpowers x ⊔ U =
                      ((Subgroup.zpowers x ⊔ U) ⊓ Subgroup.centralizer (L : Set G)) ⊔ U ∧
                    ((Subgroup.zpowers x ⊔ U) ⊓ Subgroup.centralizer (L : Set G)) ⊓ U = ⊥) ∧
                (x * x = 1 → IsQuaternionSub (R ⊓ Subgroup.centralizer ({x} : Set G)) →
                  Nat.card ↥(R ⊓ Subgroup.centralizer ({x} : Set G)) * 2 = Nat.card ↥R →
                    ∀ R₁ ∈ DSet Ω W, R₁ ≤ L → ∀ R₂ ∈ DSet Ω W, R₂ ≤ L →
                      ∃ c ∈ L ⊓ Subgroup.centralizer ({x} : Set G), conjSub c R₁ = R₂)

end CFSG.ClassicalInvolution.Asc77
