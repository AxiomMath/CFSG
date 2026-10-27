module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Complement
public import Mathlib.RepresentationTheory.Invariants
import CFSG.FeitThompson.Representations.ZeroFixedSpacePrimeComplementCentralizes
import CFSG.FeitThompson.Representations.PrimeFieldRepAlgClosedExtension
public import Mathlib.GroupTheory.Nilpotent

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Main

variable {G V : Type*} [Group G] [AddCommGroup V] {K R : Subgroup G} {p : ℕ}

theorem eq_one_of_mem_commutator_of_invariants_eq_bot_zmod [Fact p.Prime] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] [Finite G] [Group.IsSolvable G] [K.Normal]
    (hodd : Odd (Nat.card G)) (hKR : K.IsComplement' R)
    (hcop : (Nat.card K).Coprime (Nat.card R)) (hr : (Nat.card R).Prime)
    (hp : ¬ p ∣ Nat.card G) (ρ : Representation (ZMod p) G V)
    (hCV : Representation.invariants (ρ.comp R.subtype) = ⊥)
    {x : G} (hx : x ∈ (⁅K, R⁆ : Subgroup G)) : ρ x = 1 := by
  set L := AlgebraicClosure (ZMod p) with hL
  have hk : (Nat.card G : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hp
  have hkL : (Nat.card G : L) ≠ 0 :=
    Representation.natCard_ne_zero_of_baseField (G := G) L hk
  have hCVL : Representation.invariants
      ((Representation.baseChange L ρ).comp R.subtype) = ⊥ := by
    rw [← Submodule.finrank_eq_zero, Representation.finrank_invariants_baseChange_restrict, hCV]
    simp
  have h1 : x ∈ (Representation.baseChange L ρ).ker :=
    eq_one_of_mem_commutator_of_invariants_eq_bot hodd hKR hcop hr hkL _ hCVL hx
  rwa [Representation.ker_baseChange, MonoidHom.mem_ker] at h1

theorem eq_one_of_generalLinearGroup_of_mem_commutator_of_invariants_eq_bot_zmod
    [Fact p.Prime] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] [Finite G]
    [Group.IsSolvable G] [K.Normal]
    (hodd : Odd (Nat.card G)) (hKR : K.IsComplement' R)
    (hcop : (Nat.card K).Coprime (Nat.card R)) (hr : (Nat.card R).Prime)
    (hp : ¬ p ∣ Nat.card G) (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hCV : Representation.invariants
      (((Units.coeHom (V →ₗ[ZMod p] V)).comp ρ).comp R.subtype) = ⊥)
    {x : G} (hx : x ∈ (⁅K, R⁆ : Subgroup G)) : ρ x = 1 := by
  refine Units.ext ?_
  simpa using eq_one_of_mem_commutator_of_invariants_eq_bot_zmod hodd hKR hcop hr hp
    ((Units.coeHom (V →ₗ[ZMod p] V)).comp ρ) hCV hx

theorem forall_apply_eq_self_of_mem_commutator_of_invariants_eq_bot_zmod
    [Fact p.Prime] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] [Finite G]
    [Group.IsSolvable G] [K.Normal]
    (hodd : Odd (Nat.card G)) (hKR : K.IsComplement' R)
    (hcop : (Nat.card K).Coprime (Nat.card R)) (hr : (Nat.card R).Prime)
    (hp : ¬ p ∣ Nat.card G) (ρ : Representation (ZMod p) G V)
    (hCV : Representation.invariants (ρ.comp R.subtype) = ⊥) :
    ∀ x ∈ (⁅K, R⁆ : Subgroup G), ∀ v : V, ρ x v = v := by
  intro x hx v
  rw [eq_one_of_mem_commutator_of_invariants_eq_bot_zmod hodd hKR hcop hr hp ρ hCV hx]
  simp

end Main

end CFSG.FeitThompson
