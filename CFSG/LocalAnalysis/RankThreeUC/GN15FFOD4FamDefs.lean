module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open scoped Pointwise

section Perm

variable {H : Type*} [Group H] {V : Type*}

@[expose] def fixSet (σ : H →* Equiv.Perm V) (T : Subgroup H) : Set V :=
  {v | ∀ t ∈ T, σ t v = v}

@[expose] def setStab (σ : H →* Equiv.Perm V) (C : Set V) : Subgroup H :=
  (MulAction.stabilizer (Equiv.Perm V) C).comap σ

@[expose] def sylowFamilyOn (σ : H →* Equiv.Perm V) (S : Set V) : Set (Subgroup H) :=
  Set.range fun T : Sylow 2 H => setStab σ (S ∩ fixSet σ (T : Subgroup H))

end Perm

section Module

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable (ρ : Representation (ZMod 2) G W) (L : Subgroup G)

@[expose] def permRep : L →* Equiv.Perm W where
  toFun l :=
    { toFun := ρ (l : G)
      invFun := ρ ((l : G)⁻¹)
      left_inv := fun v => by
        change (ρ ((l : G)⁻¹) * ρ (l : G)) v = v
        rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      right_inv := fun v => by
        change (ρ (l : G) * ρ ((l : G)⁻¹)) v = v
        rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] }
  map_one' := by
    ext v
    change ρ ((1 : L) : G) v = v
    rw [OneMemClass.coe_one, map_one, Module.End.one_apply]
  map_mul' a b := by
    ext v
    change ρ ((a * b : L) : G) v = ρ (a : G) (ρ (b : G) v)
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]

@[expose] def IsInv (S : Submodule (ZMod 2) W) : Prop :=
  ∀ l ∈ L, ∀ v ∈ S, ρ l v ∈ S

@[expose] def IsSimpleL (S : Submodule (ZMod 2) W) : Prop :=
  S ≠ ⊥ ∧ IsInv ρ L S ∧
    ∀ S' : Submodule (ZMod 2) W, S' ≤ S → IsInv ρ L S' → S' = ⊥ ∨ S' = S

@[expose] def modFamily (S : Submodule (ZMod 2) W) : Set (Subgroup L) :=
  sylowFamilyOn (permRep ρ L) (S : Set W)

@[expose] def famBar (S : Submodule (ZMod 2) W) : Set (Subgroup (L ⧸ Subgroup.center L)) :=
  (fun H => H.map (QuotientGroup.mk' (Subgroup.center L))) '' modFamily ρ L S

@[expose] def famSum (Ψ : Set (Subgroup (L ⧸ Subgroup.center L))) : Submodule (ZMod 2) W :=
  ⨆ (S : Submodule (ZMod 2) W) (_ : IsSimpleL ρ L S) (_ : famBar ρ L S = Ψ), S

end Module

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
