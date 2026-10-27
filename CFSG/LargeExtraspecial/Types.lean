module

public import CFSG.LargeExtraspecial.Transport
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsTypeA (q : QuadraticForm (ZMod 2) V) (t : V ≃ₗ[ZMod 2] V) (l : ℕ) : Prop :=
  (∀ v, q (t v) = q v) ∧ t ≠ 1 ∧ t * t = 1 ∧ finrank (ZMod 2) (commSpace t) = l ∧
    ∀ x ∈ commSpace t, q x = 0

@[expose] def IsTypeC (q : QuadraticForm (ZMod 2) V) (t : V ≃ₗ[ZMod 2] V) (l : ℕ) : Prop :=
  (∀ v, q (t v) = q v) ∧ t ≠ 1 ∧ t * t = 1 ∧ finrank (ZMod 2) (commSpace t) = l ∧ Even l ∧
    ∃ x ∈ commSpace t, q x ≠ 0

@[expose] def IsTypeB (q : QuadraticForm (ZMod 2) V) (t : V ≃ₗ[ZMod 2] V) (l : ℕ) : Prop :=
  (∀ v, q (t v) = q v) ∧ t * t = 1 ∧ finrank (ZMod 2) (commSpace t) = l ∧ Odd l

@[expose] def IsSpTypeA (f : LinearMap.BilinForm (ZMod 2) V) (t : V ≃ₗ[ZMod 2] V) (l : ℕ) :
    Prop :=
  (∀ u v, f (t u) (t v) = f u v) ∧ t ≠ 1 ∧ t * t = 1 ∧ finrank (ZMod 2) (commSpace t) = l ∧
    ∀ v, f v (t v) = 0

@[expose] def IsSpTypeC (f : LinearMap.BilinForm (ZMod 2) V) (t : V ≃ₗ[ZMod 2] V) (l : ℕ) :
    Prop :=
  (∀ u v, f (t u) (t v) = f u v) ∧ t ≠ 1 ∧ t * t = 1 ∧ finrank (ZMod 2) (commSpace t) = l ∧
    Even l ∧ ∃ v, f v (t v) ≠ 0

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

@[expose] def IsTypeAOn (g : S.M) (l : ℕ) : Prop := IsTypeA S.q (S.ρ g : _) l

@[expose] def IsTypeCOn (g : S.M) (l : ℕ) : Prop := IsTypeC S.q (S.ρ g : _) l

@[expose] def IsTypeBOn (g : S.M) (l : ℕ) : Prop := IsTypeB S.q (S.ρ g : _) l

@[expose] noncomputable def La (g : G) : Subgroup G := S.QG ⊔ (S.Qa g ⊓ S.M)

@[expose] noncomputable def L0 (g : G) : Subgroup G := S.Qa g ⊓ S.M

end Setting

end CFSG.LargeExtraspecial
