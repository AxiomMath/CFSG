module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Defs

public section

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup

variable {G : Type} [Group G] [Finite G]

structure G1Data {L Q : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
    (c : Config G L Q n θ z) (T S₀ D : Subgroup G) : Prop where
  hH : HData θ c.hn8 z T
  S₀_le : S₀ ≤ N0 θ c.hn8 z ⊓ centralizer ({z} : Set G)
  S₀_p : IsPGroup 2 S₀
  S₀_card : Nat.card S₀ = 2 ^ 7
  S₀_norm : S₀ ≤ normalizer (T : Set G)
  D_le_S₀ : D ≤ S₀
  D_le_L : D ≤ L
  D_card : Nat.card D = 8
  D_inf : D ⊓ T = ⊥

@[expose] def TB (T S₀ : Subgroup G) : Subgroup G := T ⊔ S₀

@[expose] def MB (T D : Subgroup G) : Subgroup G := T ⊔ D

structure TBFacts (T S₀ D : Subgroup G) (z : G) : Prop where
  normal_e64 : ∀ N : Subgroup G, N ≤ TB T S₀ → (∀ g ∈ TB T S₀, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
    (∀ x ∈ N, x ^ 2 = 1) → Nat.card N = 64 → N ≠ T →
      Nat.card (N ⊓ centralizer ({z} : Set G) : Subgroup G) = 16
  mem_MB : ∀ x ∈ TB T S₀, x ∉ T → x ^ 2 = 1 →
    Nat.card (T ⊓ centralizer ({x} : Set G) : Subgroup G) = 16 → x ∈ MB T D
  conj_cent : ∀ x ∈ MB T D, x ∉ T → orderOf x = 2 →
    (Nat.card (TB T S₀ ⊓ centralizer ({x} : Set G) : Subgroup G) = 2 ^ 8 ∨
      Nonempty ((TB T S₀ ⊓ centralizer ({x} : Set G) : Subgroup G) ≃*
        (TB T S₀ ⊓ centralizer ({z} : Set G) : Subgroup G))) →
      ∃ g ∈ TB T S₀, g * x * g⁻¹ ∈ centralizer ({z} : Set G)

@[expose] def Sec4TwoElemN0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (x : G),
      x ∈ N0 θ c.hn8 z ⊓ centralizer ({z} : Set G) → ∀ k : ℕ, x ^ 2 ^ k = 1 →
        ∃ m ∈ L, x = m ∨ x = z * m

@[expose] def Sec4CentSylowCard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z)
    (P : Sylow 2 (centralizer ({z} : Set G))),
      (IsASmall L n z → Nat.card P = 2 ^ 7) ∧ (¬ IsASmall L n z → Nat.card P = 2 ^ 8)

@[expose] def Sec4ExistsG1Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
      HData θ c.hn8 z T → ∃ S₀ D : Subgroup G, G1Data c T S₀ D

@[expose] def Sec4TBFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T S₀ D : Subgroup G),
      G1Data c T S₀ D → TBFacts T S₀ D z

end CFSG.OddStandard.AltStdSmall4
