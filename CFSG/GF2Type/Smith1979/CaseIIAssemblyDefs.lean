module

public import CFSG.GF2Type.Smith1979.CaseIIA8
public import CFSG.Open.StatedDefs
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.Open.QuasithinDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

@[expose] def U43Frob56Free : Prop :=
  ∀ {X : Type} [Group X], CFSG.Open.StatedClassicalModel X .PSU 4 3 1 → ∀ {y : X},
    orderOf y = 7 → ∀ S : Subgroup X, (∀ s ∈ S, s * s = 1) → Nat.card S = 8 →
      (∀ s ∈ S, y * s * y⁻¹ ∈ S) → (∀ s ∈ S, y * s * y⁻¹ = s → s = 1) → False

@[expose] def RderFacts : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}, Data S g t →
    S4.CentralExtInput.{0} →
      (∃ y ∈ Rder S g t, orderOf y = 7 ∧
          (∀ s ∈ Rder S g t ⊓ Nbar S g t, y * s * y⁻¹ = s → s = 1) ∧
          ∀ x ∈ Rder S g t, x * y = y * x → x ∈ Subgroup.zpowers y) ∧
        (∃ x ∈ Rder S g t, orderOf x = 6) ∧
        (∀ y ∈ Rder S g t, ∀ s ∈ Rder S g t ⊓ Nbar S g t,
          y * s * y⁻¹ ∈ Rder S g t ⊓ Nbar S g t)

end CFSG.GF2Type.Smith1979.Case2
