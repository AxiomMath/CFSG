module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.Complement
public import Mathlib.Algebra.Field.ZMod
import CFSG.FeitThompson.Representations.AlgClosedFrobeniusComplementDerivedTrivial
import CFSG.FeitThompson.Representations.PrimeFieldRepAlgClosedExtension
public import Mathlib.GroupTheory.Nilpotent

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section AnyField

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] {K R : Subgroup G}

theorem eq_one_of_mem_commutator_of_finrank_invariants_eq_one_of_natCard_ne_zero
    [FiniteDimensional k V] [Finite G]
    (hK : K.Normal) (hKR : Subgroup.IsComplement' K R) (hK1 : K ≠ ⊥) (hR1 : R ≠ ⊥)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ Subgroup.centralizer {x} = ⊥)
    (hsol : Group.IsSolvable ↥K) (hr : Nat.Prime (Nat.card ↥R))
    (hk : (Nat.card G : k) ≠ 0) (ρ : Representation k G V)
    (hfinrank : Module.finrank k (Representation.invariants (ρ.comp R.subtype)) = 1)
    {x : G} (hx : x ∈ ⁅K, K⁆) : ρ x = 1 := by
  set L := AlgebraicClosure k
  have hkL : (Nat.card G : L) ≠ 0 := Representation.natCard_ne_zero_of_baseField L hk
  have hfr : Module.finrank L
      (Representation.invariants ((Representation.baseChange L ρ).comp R.subtype)) = 1 := by
    rw [Representation.finrank_invariants_baseChange_restrict, hfinrank]
  have h := eq_one_of_mem_commutator_of_finrank_invariants_eq_one hK hKR hK1 hR1 hC hsol hr hkL
    (Representation.baseChange L ρ) hfr hx
  have hker : x ∈ (Representation.baseChange L ρ).ker := h
  rwa [Representation.ker_baseChange] at hker

end AnyField

variable {p : ℕ} [Fact p.Prime] {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod p) V]
variable {K R : Subgroup G}

theorem eq_one_of_mem_commutator_of_finrank_invariants_eq_one_zmod
    [FiniteDimensional (ZMod p) V] [Finite G]
    (hK : K.Normal) (hKR : Subgroup.IsComplement' K R) (hK1 : K ≠ ⊥) (hR1 : R ≠ ⊥)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ Subgroup.centralizer {x} = ⊥)
    (hsol : Group.IsSolvable ↥K) (hr : Nat.Prime (Nat.card ↥R))
    (hp : ¬ p ∣ Nat.card G) (ρ : Representation (ZMod p) G V)
    (hfinrank : Module.finrank (ZMod p) (Representation.invariants (ρ.comp R.subtype)) = 1)
    {x : G} (hx : x ∈ ⁅K, K⁆) : ρ x = 1 :=
  eq_one_of_mem_commutator_of_finrank_invariants_eq_one_of_natCard_ne_zero hK hKR hK1 hR1 hC hsol
    hr (fun h => hp ((ZMod.natCast_eq_zero_iff _ _).1 h)) ρ hfinrank hx

theorem eq_one_of_generalLinearGroup_of_mem_commutator_of_finrank_invariants_eq_one_zmod
    [FiniteDimensional (ZMod p) V] [Finite G]
    (hK : K.Normal) (hKR : Subgroup.IsComplement' K R) (hK1 : K ≠ ⊥) (hR1 : R ≠ ⊥)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ Subgroup.centralizer {x} = ⊥)
    (hsol : Group.IsSolvable ↥K) (hr : Nat.Prime (Nat.card ↥R))
    (hp : ¬ p ∣ Nat.card G) (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hfinrank : Module.finrank (ZMod p) (Representation.invariants
      (((Units.coeHom (V →ₗ[ZMod p] V)).comp ρ).comp R.subtype)) = 1)
    {x : G} (hx : x ∈ ⁅K, K⁆) : ρ x = 1 := by
  have h := eq_one_of_mem_commutator_of_finrank_invariants_eq_one_zmod hK hKR hK1 hR1 hC hsol hr hp
    ((Units.coeHom (V →ₗ[ZMod p] V)).comp ρ) hfinrank hx
  refine Units.ext ?_
  simpa using h

theorem forall_apply_eq_self_of_mem_commutator_of_finrank_invariants_eq_one_zmod
    [FiniteDimensional (ZMod p) V] [Finite G]
    (hK : K.Normal) (hKR : Subgroup.IsComplement' K R) (hK1 : K ≠ ⊥) (hR1 : R ≠ ⊥)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ Subgroup.centralizer {x} = ⊥)
    (hsol : Group.IsSolvable ↥K) (hr : Nat.Prime (Nat.card ↥R))
    (hp : ¬ p ∣ Nat.card G) (ρ : Representation (ZMod p) G V)
    (hfinrank : Module.finrank (ZMod p) (Representation.invariants (ρ.comp R.subtype)) = 1) :
    ∀ x ∈ ⁅K, K⁆, ∀ v : V, ρ x v = v := by
  intro x hx v
  rw [eq_one_of_mem_commutator_of_finrank_invariants_eq_one_zmod hK hKR hK1 hR1 hC hsol hr hp ρ
    hfinrank hx]
  simp

end CFSG.FeitThompson
