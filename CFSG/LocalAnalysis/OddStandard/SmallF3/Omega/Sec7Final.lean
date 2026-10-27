module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec7E (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B E : Subgroup G) : Prop where
  choice : Sec7Choice G t L S z g B
  sylow : IsSylow2Of E (MSub S B ⊓ centralizer (B : Set G))
  A_le : ASub S B ≤ E
  quot : QuotEquivTo E (ASub S B) E16
  comm_t : ∀ e ∈ E, e * t * e⁻¹ * t⁻¹ ∈ B
  trans : ∀ x ∈ cosetSet t B, ∃ e ∈ E, e * t * e⁻¹ = x
  cent_t : ∀ e ∈ E, e * t = t * e → e ∈ ASub S B
  sq_mem : ∀ e ∈ E, e ^ 2 ∈ B

structure Sec7U (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B E U : Subgroup G) : Prop where
  hE : Sec7E G t L S z g B E
  le : U ≤ E
  B_le : B ≤ U
  card : Nat.card U = 2 ^ 8
  sup : zpowers t ⊔ U = E
  inf : zpowers t ⊓ U = ⊥
  inv : ∀ n ∈ L ⊓ MSub S B, ∀ u ∈ U, ∃ u' ∈ U, ∃ o ∈ oddCoreIn (MSub S B), n * u * n⁻¹ = u' * o

@[expose] def Asc82Final7U : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
    Sec7E G t L S z g B E → ∃ U : Subgroup G, Sec7U G t L S z g B E U

@[expose] def Asc82Final7E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec7Choice G t L S z g B → ∃ E U : Subgroup G, Sec7U G t L S z g B E U

@[expose] def Asc82Final7Prince : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B E U : Subgroup G),
    Sec7U G t L S z g B E U → IsElemAb2 U 8 ∨ Nonempty (U ≃* Z4Pow4)

@[expose] def Asc82Final7Y : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B E U : Subgroup G),
    Sec7U G t L S z g B E U → ∀ b ∈ B, b ≠ 1 → InducesTypeSome L b 6 1 2 (-1) →
      ∃ Y : Subgroup G, IsComponentIn Y (centralizer ({b} : Set G)) ∧
        (Y.subgroupOf (centralizer ({b} : Set G))).Normal ∧ InFStar Y ∧ InCStar Y ∧
        layerCent L b ≤ Y ∧ (IsOmega5 Y ∨ IsOmega6Plus Y ∨ IsOmega6Minus Y ∨ IsL281 Y) ∧
        E ≤ normalizer (Y : Set G) ∧ centralizer (Y : Set G) ⊓ ASub S B = zpowers b ∧
        IsCyclic ↥(E ⊓ centralizer (Y : Set G))

@[expose] def Asc82AbelAutBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y U : Subgroup G), IsQuasisimple Y →
    U ≤ normalizer (Y : Set G) → IsPGroup 2 U →
      (∀ a ∈ autIn U Y, ∀ b ∈ autIn U Y, a * b = b * a) →
        (IsOmega5 Y → Nat.card (autIn U Y) ≤ 16) ∧ (IsL281 Y → Nat.card (autIn U Y) ≤ 16) ∧
          (IsOmega6Plus Y → Nat.card (autIn U Y) ≤ 32)

end CFSG.OddStandard.SmallF3.Omega
