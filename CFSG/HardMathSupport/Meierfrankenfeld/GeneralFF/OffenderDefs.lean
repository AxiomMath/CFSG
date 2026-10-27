module

public import CFSG.RankThree.FFModules.Offenders

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsInvariant (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) : Prop :=
  ∀ a ∈ A, ∀ u ∈ U, ρ a u ∈ U

@[expose] def cenOn (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) : Subgroup G where
  carrier := {g | g ∈ A ∧ ∀ u ∈ U, ρ g u = u}
  mul_mem' {a b} ha hb := ⟨A.mul_mem ha.1 hb.1, fun u hu => by
    rw [map_mul, Module.End.mul_apply, hb.2 u hu, ha.2 u hu]⟩
  one_mem' := ⟨A.one_mem, fun u _ => by simp⟩
  inv_mem' {a} ha := ⟨A.inv_mem ha.1, fun u hu => by
    have h := ha.2 u hu
    calc ρ a⁻¹ u = ρ a⁻¹ (ρ a u) := by rw [h]
      _ = u := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl⟩

@[expose] def fixOn (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  U ⊓ fixSub ρ A

@[expose] def commOn (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {w | ∃ a ∈ A, ∃ u ∈ U, w = ρ a u - u}

@[expose] def IsElemAbelianOn (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, (∀ u ∈ U, ρ (a * b * a⁻¹ * b⁻¹) u = u) ∧ (∀ u ∈ U, ρ (a * a) u = u)

@[expose] def IsOffenderOn (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) : Prop :=
  IsElemAbelianOn ρ A U ∧
    Nat.card U * Nat.card (cenOn ρ A U) ≤ Nat.card A * Nat.card (fixOn ρ A U)

@[expose] def IsBestOffenderOn (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) : Prop :=
  IsElemAbelianOn ρ A U ∧
    ∀ B : Subgroup G, B ≤ A → Nat.card B * Nat.card (fixOn ρ B U) ≤
      Nat.card A * Nat.card (fixOn ρ A U)

@[expose] def IsQuadraticOn (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) : Prop :=
  commOn ρ A U ≤ fixSub ρ A

theorem mem_cenOn {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    {U : Submodule (ZMod 2) V} {g : G} :
    g ∈ cenOn ρ A U ↔ g ∈ A ∧ ∀ u ∈ U, ρ g u = u :=
  Iff.rfl

theorem mem_fixOn {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    {U : Submodule (ZMod 2) V} {v : V} :
    v ∈ fixOn ρ A U ↔ v ∈ U ∧ ∀ a ∈ A, ρ a v = v :=
  Iff.rfl

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
