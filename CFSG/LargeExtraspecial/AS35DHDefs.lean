module

public import CFSG.LargeExtraspecial.AS35DStmt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace Asc77

variable {G : Type} [Group G]

@[expose] def conjIn (z : G) (H : Subgroup G) : Set G := {x | ∃ h ∈ H, h * z * h⁻¹ = x}

theorem conj_mem_conjIn {z : G} {H : Subgroup G} {h : G} (hh : h ∈ H) :
    h * z * h⁻¹ ∈ conjIn z H :=
  ⟨h, hh, rfl⟩

theorem self_mem_conjIn (z : G) (H : Subgroup G) : z ∈ conjIn z H :=
  ⟨1, H.one_mem, by group⟩

theorem conj_mem_conjIn_of_mem {z : G} {H : Subgroup G} {h x : G} (hh : h ∈ H)
    (hx : x ∈ conjIn z H) : h * x * h⁻¹ ∈ conjIn z H := by
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨h * k, H.mul_mem hh hk, by group⟩

@[expose, instance_reducible] def conjMulAction (z : G) (H : Subgroup G) :
    MulAction H (conjIn z H) where
  smul h x := ⟨h * x * (h : G)⁻¹, conj_mem_conjIn_of_mem h.2 x.2⟩
  one_smul x := Subtype.ext (by
    change (1 : G) * x * 1⁻¹ = x
    group)
  mul_smul a b x := Subtype.ext (by
    change (a * b : G) * x * (a * b : G)⁻¹ = a * (b * x * (b : G)⁻¹) * (a : G)⁻¹
    group)

@[expose] def conjAct (z : G) (H : Subgroup G) : H →* Equiv.Perm (conjIn z H) :=
  letI := conjMulAction z H
  MulAction.toPermHom H (conjIn z H)

theorem conjAct_apply {z : G} {H : Subgroup G} (h : H) (x : conjIn z H) :
    ((conjAct z H h x : conjIn z H) : G) = h * x * (h : G)⁻¹ := rfl

@[expose] def centerIn (z : G) (H : Subgroup G) : Subgroup G :=
  closure (conjIn z H) ⊓ centralizer (H : Set G)

@[expose] def IsSThreeAt (z : G) (H : Subgroup G) : Prop :=
  (conjIn z H).ncard = 3 ∧ (∀ a ∈ conjIn z H, ∀ b ∈ conjIn z H, a * b = b * a) ∧
    Nat.card (closure (conjIn z H)) = 4 * Nat.card (centerIn z H) ∧
    Function.Surjective (conjAct z H)

@[expose] def IsAFiveAt (z : G) (H : Subgroup G) : Prop :=
  ∃ (_ : Fintype (conjIn z H)) (_ : DecidableEq (conjIn z H)), (conjIn z H).ncard = 5 ∧
    (∀ a ∈ conjIn z H, ∀ b ∈ conjIn z H, a * b = b * a) ∧
    Nat.card (closure (conjIn z H)) = 16 * Nat.card (centerIn z H) ∧
    (∀ h : H, Equiv.Perm.sign (conjAct z H h) = 1) ∧
    ∀ σ : Equiv.Perm (conjIn z H), Equiv.Perm.sign σ = 1 → ∃ h : H, conjAct z H h = σ

end Asc77

namespace Setting

variable {G : Type} [Group G] (S : Setting G)

abbrev zConj (H : Subgroup G) : Set G := Asc77.conjIn S.z H

theorem zConj_subset_zGen (H : Subgroup G) : S.zConj H ⊆ S.zGen := by
  rintro _ ⟨h, -, rfl⟩
  exact S.conj_mem_zGen h

@[expose] def IsHSet (H : Subgroup G) : Prop :=
  S.QG ≤ H ∧ CFSG.pCore 2 H ≠ ⊥ ∧ ¬ H ≤ S.M

@[expose] def IsHStar (H : Subgroup G) : Prop :=
  S.IsHSet H ∧ ∀ H' : Subgroup G, S.IsHSet H' → H' ≤ H → H' = H

@[expose] def ESet : Set G :=
  {t | ∃ h : G, h * S.z * h⁻¹ = t ∧ S.IsHStar (S.QG ⊔ S.Qa h) ∧
    (S.zConj (S.QG ⊔ S.Qa h)).ncard = 5}

@[expose] def DSet : Set G := {t | t ∈ S.ESet ∧ ¬ IsConj S.z (S.z * t)}

end Setting

end CFSG.LargeExtraspecial
