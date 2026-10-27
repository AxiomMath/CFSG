module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.LargeExtraspecial.Timmesfeld

open CFSG.Assembly Subgroup

open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def fStar (M : Subgroup G) : Subgroup G := (CFSG.generalizedFitting M).map M.subtype

@[expose] def IsExtraspecial2 (Q : Subgroup G) : Prop :=
  IsPGroup 2 Q ∧ ⁅Q, Q⁆ = (Subgroup.center Q).map Q.subtype ∧ Nat.card (⁅Q, Q⁆ : Subgroup G) = 2

@[expose] def HasWidth (Q : Subgroup G) (n : ℕ) : Prop := Nat.card Q = 2 ^ (2 * n + 1)

@[expose] def Qa (a : G) : Subgroup G := fStar (centralizer ({a} : Set G))

@[expose] def M (z : G) : Subgroup G := centralizer ({z} : Set G)

@[expose] def L (z a : G) : Subgroup G := fStar (M z) ⊔ (Qa a ⊓ M z)

@[expose] def L0 (z a : G) : Subgroup G := Qa a ⊓ M z

structure Section3.Context (G : Type) [Group G] [Finite G] (z : G) (n : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  involution : z ≠ 1 ∧ z ^ 2 = 1
  extraspecial : IsExtraspecial2 (fStar (M z))
  width : HasWidth (fStar (M z)) n

@[expose] def IsSpecial (z a : G) : Prop :=
  (∃ g : G, a = g * z * g⁻¹) ∧ a ∈ fStar (M z) ∧ a ∉ Subgroup.zpowers z

@[expose] def IsA2Involution (z t : G) : Prop :=
  t ∈ M z ∧
  (∃ x ∈ fStar (M z), ⁅x, t⁆ ∉ Subgroup.zpowers z) ∧
  (∀ x ∈ fStar (M z), ⁅x, t ^ 2⁆ ∈ Subgroup.zpowers z) ∧
  Nat.card (Subgroup.closure {y : G | ∃ x ∈ fStar (M z), y = ⁅x, t⁆} ⊔ Subgroup.zpowers z :
    Subgroup G) = 2 ^ 3 ∧
  (∀ x ∈ fStar (M z), ⁅x, t * x * t⁻¹⁆ = 1)

namespace Section4

structure Context (G : Type) [Group G] [Finite G] (z a : G) (n : ℕ) : Prop where
  section3 : Section3.Context G z n
  special : IsSpecial z a
  centralizer_eq : ∀ x ∈ fStar (M z),
    (∀ l ∈ L z a, ⁅x, l⁆ ∈ Subgroup.zpowers z) ↔ x ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers a
  width_gt : 2 < n

end Section4

namespace Section5

structure Context (G : Type) [Group G] [Finite G] (z a : G) (n : ℕ) : Prop where
  section4 : Section4.Context G z a n
  no_a2 : ∀ t ∈ L z a, t ∉ fStar (M z) → ¬ IsA2Involution z t

end Section5

namespace Section12

structure Context (G : Type) [Group G] [Finite G] (z a : G) (n : ℕ) : Prop where
  section3 : Section3.Context G z n
  special : IsSpecial z a
  exists_a2 : ∃ t ∈ L z a, t ∉ fStar (M z) ∧ IsA2Involution z t

end Section12

end CFSG.LargeExtraspecial.Timmesfeld
