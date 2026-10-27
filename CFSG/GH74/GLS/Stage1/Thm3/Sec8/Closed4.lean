module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

@[expose] def Concl810 {G : Type} [Group G] (S K₁ W₂ : Subgroup G) (h t : G) (Sg : Subgroup G) : Prop :=
  zpowers h ⊔ zpowers t ≤ Sg ∧ Aof S K₁ W₂ h ⊓ Sg = ⊥ ∧
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

@[expose] def Final81 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G) (Y D : Subgroup G)
    (t w : G), Setup8 G z S K₁ K₂ W₁ W₂ U u h → Nat.card ↥(Pof S K₁) = 8 → Nat.card ↥S = 2 ^ 7 →
      Concl86 z S K₁ W₂ U u h Y D t w → ∀ E₁ E₂ : Subgroup G, EData Y U E₁ E₂ →
        (∃ Sg : Subgroup G, Concl810 S K₁ W₂ h t Sg) → L4U4TermType G z S

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
