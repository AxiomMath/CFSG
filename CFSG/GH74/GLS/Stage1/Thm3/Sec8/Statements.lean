module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Closed

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

@[expose] def Lemma8_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G),
    Setup8 G z S K₁ K₂ W₁ W₂ U u h → Nat.card ↥(Pof S K₁) = 8 → 2 ^ 7 ≤ Nat.card ↥S →
      ∃ w ∈ Wsub S U, ⁅w, h⁆ ∉ Aof S K₁ W₂ h

@[expose] def Concl86 {G : Type} [Group G] (z : G) (S K₁ W₂ U : Subgroup G) (u h : G)
    (Y D : Subgroup G) (t w : G) : Prop :=
  S ⊔ zpowers h = Y ⊔ zpowers h ⊔ D ∧ S = Y ⊔ D ∧
  (Aof S K₁ W₂ h ≤ Y ∧ Y ≤ S ⊔ zpowers h ∧ NormedBy Y (S ⊔ zpowers h) ∧
    Nonempty (↥Y ≃* Bg.TwoGroups.SylSL3_4) ∧ (∀ y ∈ Y, h * y = y * h → y = 1)) ∧
  (D = zpowers t ⊔ zpowers w ∧
    zpowers h ⊔ D = (S ⊔ zpowers h) ⊓ normalizer (zpowers h : Set G) ∧
    D = S ⊓ normalizer (zpowers h : Set G)) ∧
  (t ∈ Pz S z ∧ orderOf t = 2 ∧ t⁻¹ * u * t = u * z ∧ t⁻¹ * h * t = h⁻¹) ∧
  (D ⊓ centralizer (U : Set G) = zpowers w ∧ w * h = h * w) ∧
  ((w = 1 ∧ ∃ _ : ((zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ D)).Normal,
      Nonempty ((↥(zpowers h ⊔ D) ⧸ (zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ D)) ≃*
        Equiv.Perm (Fin 3))) ∨
   ((∀ x ∈ Aof S K₁ W₂ h, w * x * w⁻¹ = x⁻¹) ∧
    ∃ _ : ((zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ D)).Normal,
      Nonempty ((↥(zpowers h ⊔ D) ⧸ (zpowers (h ^ 3)).subgroupOf (zpowers h ⊔ D)) ≃*
        DihedralGroup 6)))

@[expose] def Lemma8_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G),
    Setup8 G z S K₁ K₂ W₁ W₂ U u h → Nat.card ↥(Pof S K₁) = 8 → 2 ^ 7 ≤ Nat.card ↥S →
      ∃ (Y D : Subgroup G) (t w : G), Concl86 z S K₁ W₂ U u h Y D t w

@[expose] def Lemma8_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G) (Y D : Subgroup G)
    (t w : G), Setup8 G z S K₁ K₂ W₁ W₂ U u h → Nat.card ↥(Pof S K₁) = 8 → 2 ^ 7 ≤ Nat.card ↥S →
      Concl86 z S K₁ W₂ U u h Y D t w → ∀ E₁ E₂ : Subgroup G, EData Y U E₁ E₂ →
        Nat.card ↥S = 2 ^ 7

@[expose] def Lemma8_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G) (Y D : Subgroup G)
    (t w : G), Setup8 G z S K₁ K₂ W₁ W₂ U u h → Nat.card ↥(Pof S K₁) = 8 → Nat.card ↥S = 2 ^ 7 →
      Concl86 z S K₁ W₂ U u h Y D t w → ∀ E₁ E₂ : Subgroup G, EData Y U E₁ E₂ →
        ∃ Sg : Subgroup G, zpowers h ⊔ zpowers t ≤ Sg ∧ Aof S K₁ W₂ h ⊓ Sg = ⊥ ∧
          S ⊔ zpowers h = Aof S K₁ W₂ h ⊔ Sg ∧
          (∃ _ : ((zpowers (h ^ 3)).subgroupOf Sg).Normal,
            Nonempty ((↥Sg ⧸ (zpowers (h ^ 3)).subgroupOf Sg) ≃* Equiv.Perm (Fin 4))) ∧
          ∀ Sg' : Subgroup G, zpowers h ⊔ zpowers t ≤ Sg' → Aof S K₁ W₂ h ⊓ Sg' = ⊥ →
            S ⊔ zpowers h = Aof S K₁ W₂ h ⊔ Sg' →
            (∃ _ : ((zpowers (h ^ 3)).subgroupOf Sg').Normal,
              Nonempty ((↥Sg' ⧸ (zpowers (h ^ 3)).subgroupOf Sg') ≃* Equiv.Perm (Fin 4))) →
              ∃ α : MulAut ↥(Aof S K₁ W₂ h),
                (∀ x ∈ Sg, ∃ x' ∈ Sg', ∀ a b : ↥(Aof S K₁ W₂ h), (b : G) = x * a * x⁻¹ →
                  ((α b : ↥(Aof S K₁ W₂ h)) : G) = x' * ((α a : ↥(Aof S K₁ W₂ h)) : G) * x'⁻¹) ∧
                (∀ x' ∈ Sg', ∃ x ∈ Sg, ∀ a b : ↥(Aof S K₁ W₂ h), (b : G) = x * a * x⁻¹ →
                  ((α b : ↥(Aof S K₁ W₂ h)) : G) = x' * ((α a : ↥(Aof S K₁ W₂ h)) : G) * x'⁻¹)

@[expose] def Prop8_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    (∃ u ∈ Pz S z, IsConj z u ∧ u ≠ z) → G2TermType G z S ∨ L4U4TermType G z S

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
