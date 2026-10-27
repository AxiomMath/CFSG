module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

@[expose] def Concl73 {G : Type} [Group G] (z : G) (S K₁ K₂ : Subgroup G) : Prop :=
  (Pz S z).relIndex (S1 S K₁) ≤ 2 ∧ Qof S K₁ = Pof S K₂ ∧ Qof S K₂ = Pof S K₁

@[expose] def Concl74c {G : Type} [Group G] (z t : G) : Prop :=
  (∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj (t * z) x) ∧ ¬ IsConj z (t * z) ∧
    IsHalfTwoCentral (t * z)

@[expose] def Concl76 {G : Type} [Group G] (z : G) (S : Subgroup G) (t : G) (D : Subgroup G)
    (d₀ : G) : Prop :=
  IsConj z (z * d₀ * t) ∧ (∃ y ∈ D, y ∉ Pz S z ∧ y * y = d₀) ∧
    (∀ x ∈ S, orderOf x = 2 → x ∈ Pz S z ⊔ zpowers t)

@[expose] def Lemma7_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ),
    Cfg7 G z S K₁ K₂ t u q → Concl73 z S K₁ K₂

@[expose] def Lemma7_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ),
    Cfg7 G z S K₁ K₂ t u q → Concl73 z S K₁ K₂ →
      (∃ D : Subgroup G, Data74 z S K₁ K₂ t D) ∧ Concl74c z t

@[expose] def Lemma7_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ),
    Cfg7 G z S K₁ K₂ t u q → Concl73 z S K₁ K₂ → Concl74c z t → (Pz S z).relIndex (S1 S K₁) = 2 →
      ∀ D : Subgroup G, Data74 z S K₁ K₂ t D → ∃ n, IVK.IsDihedralTwoGroup ↥D n

@[expose] def Lemma7_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ),
    Cfg7 G z S K₁ K₂ t u q → Concl73 z S K₁ K₂ → Concl74c z t → (Pz S z).relIndex (S1 S K₁) = 2 →
      ∀ D : Subgroup G, Data74 z S K₁ K₂ t D → (∃ n, IVK.IsDihedralTwoGroup ↥D n) →
        ∀ y ∈ D, y ∉ Pz S z → orderOf y = 2 →
          ∀ w ∈ ({y, y * z} : Set G), Concl72abcf z S K₁ K₂ t q w

@[expose] def Lemma7_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ),
    Cfg7 G z S K₁ K₂ t u q → Concl73 z S K₁ K₂ → Concl74c z t → (Pz S z).relIndex (S1 S K₁) = 2 →
      ∀ D : Subgroup G, Data74 z S K₁ K₂ t D → (∃ n, IVK.IsDihedralTwoGroup ↥D n) →
        ∀ y ∈ D, y ∉ Pz S z → orderOf y = 2 →
          (IsConj z y ∧ IsConj z (y * z)) ∧
            ∃ w ∈ ({y, y * z} : Set G), IsConj z (t * w) ∧ ¬ IsConj z (t * w * z)

@[expose] def Prop7_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ),
    Cfg7 G z S K₁ K₂ t u q →
      ∃ w : G, Concl72abcf z S K₁ K₂ t q w ∧ Concl72de z t u w

@[expose] def Lemma7_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ) (w : G),
    Cfg7 G z S K₁ K₂ t u q → Concl72abcf z S K₁ K₂ t q w → Concl72de z t u w →
      Term7 z S K₁ K₂ q w

@[expose] def Prop7_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    (∀ u ∈ Pz S z, IsConj z u → u = z) →
      ∃ (q : ℕ) (w : G), Odd q ∧ 5 ≤ q ∧ HatSL2 K₁ q ∧ HatSL2 K₂ q ∧ Term7 z S K₁ K₂ q w

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
