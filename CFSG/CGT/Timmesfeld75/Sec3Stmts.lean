module

public import CFSG.CGT.Timmesfeld75.Sec3Iso
public import CFSG.CGT.Timmesfeld75.Sec3Root
public import CFSG.CGT.Timmesfeld75.Sec5Basic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

@[expose] def InducesFieldAut {G : Type} [Group G] (X M : Subgroup G)
    [(M.subgroupOf X).Normal] {F : Type} [Field F] (a : G)
    (e : ↥X ⧸ M.subgroupOf X ≃* SL(2, F)) (σ : F ≃+* F) : Prop :=
  ∃ ha : ∀ x ∈ X, a * x * a⁻¹ ∈ X, ∀ x : ↥X,
    e (QuotientGroup.mk (⟨a * x * a⁻¹, ha x x.2⟩ : ↥X)) =
      Matrix.SpecialLinearGroup.map (σ : F →+* F) (e (QuotientGroup.mk x))

@[expose] def Lemma312Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T T₁ : Subgroup G, IsWC T → Sec3Global T → Sec3IsoGlobal T → Sec3 T T₁ →
      ∀ a ∈ classD T, ∀ (_ : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal) (F : Type) (_ : Field F)
        (_ : Finite F) (_ : CharP F 2)
        (e : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* SL(2, F)) (σ : F ≃+* F),
        σ ≠ RingEquiv.refl F → InducesFieldAut (T ⊔ T₁) (cfgM T T₁) a e σ →
          Nat.card T = 16 ∧ Nat.card F = 4

@[expose] def Lemma313Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T : Subgroup G, IsWC T → Sec3Global T → Sec3IsoGlobal T → Nat.card T ≠ 16 →
      ∀ (r : ℕ) (Ts : Fin r → Subgroup G), 0 < r → Function.Injective Ts →
        (∀ i, ∃ g : G, Ts i = conjSubgroup g T) → (∃ i, Ts i = T) →
        (∀ j, (⨅ i, normIn (Ts j) (Ts i)) ≠ ⊥) →
          IsElemAbelian 2 (⨆ j, ⨅ i, normIn (Ts j) (Ts i)) ∧
          (∀ x ∈ (⨆ i, Ts i), conjSubgroup x (⨆ j, ⨅ i, normIn (Ts j) (Ts i)) =
            ⨆ j, ⨅ i, normIn (Ts j) (Ts i)) ∧
          CFSG.Timmesfeld.IsRootInvolutionSet (classDIn (⨆ i, Ts i) T)

end CFSG.CGT.Timmesfeld75
