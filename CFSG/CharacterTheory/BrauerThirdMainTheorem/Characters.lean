module

public import CFSG.CharacterTheory.Blocks.Defs
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

open CFSG
open scoped Classical

namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem trivial_isIrreducible (G : Type*) [Group G] :
    (Representation.trivial ℂ G ℂ).IsIrreducible := by
  have hnontrivial : Nontrivial (Subrepresentation (Representation.trivial ℂ G ℂ)) := by
    apply nontrivial_of_ne (⊥ : Subrepresentation (Representation.trivial ℂ G ℂ)) ⊤
    intro hequal
    have hone : (1 : ℂ) ∈ (⊥ : Subrepresentation (Representation.trivial ℂ G ℂ)) := by
      rw [hequal]
      trivial
    change (1 : ℂ) ∈ (⊥ : Submodule ℂ ℂ) at hone
    exact one_ne_zero (by simpa only [Submodule.mem_bot] using hone)
  let : Nontrivial (Subrepresentation (Representation.trivial ℂ G ℂ)) := hnontrivial
  apply IsSimpleOrder.mk
  intro subrep
  obtain hbot | htop := eq_bot_or_eq_top subrep.toSubmodule
  · left
    apply Subrepresentation.toSubmodule_injective
    exact hbot
  · right
    apply Subrepresentation.toSubmodule_injective
    exact htop

theorem trivial_character (G : Type*) [Group G] :
    (Representation.trivial ℂ G ℂ).character = (fun _ => (1 : ℂ)) := by
  funext element
  change LinearMap.trace ℂ ℂ LinearMap.id = 1
  simp [LinearMap.trace_id]

theorem trivial_mem_irr (G : Type*) [Group G] :
    (fun _ => (1 : ℂ)) ∈ BlocksIrr G := by
  exact ⟨ℂ, inferInstance, inferInstance, inferInstance, Representation.trivial ℂ G ℂ,
    trivial_isIrreducible G, trivial_character G⟩

theorem irr_conj {G : Type*} [Group G] {character : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) (element conjugator : G) :
    character (conjugator * element * conjugator⁻¹) = character element := by
  obtain ⟨space, _, _, _, representation, _, rfl⟩ := hcharacter
  exact representation.char_conj element conjugator

theorem irr_orthogonality {G : Type*} [Group G] [Finite G] {left right : G → ℂ}
    (hleft : left ∈ BlocksIrr G) (hright : right ∈ BlocksIrr G) :
    (Nat.card G : ℂ)⁻¹ * (∑ᶠ element : G, left element * right element⁻¹) =
      if left = right then 1 else 0 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  obtain ⟨leftSpace, _, _, _, leftRep, hleftRep, rfl⟩ := hleft
  obtain ⟨rightSpace, _, _, _, rightRep, hrightRep, rfl⟩ := hright
  let : leftRep.IsIrreducible := hleftRep
  let : rightRep.IsIrreducible := hrightRep
  rw [finsum_eq_sum_of_fintype]
  have horth := Representation.char_orthonormal leftRep rightRep
  by_cases hequal : leftRep.character = rightRep.character
  · have hself := Representation.char_orthonormal leftRep leftRep
    have hselfEquiv : Nonempty (leftRep.Equiv leftRep) := ⟨Representation.Equiv.refl leftRep⟩
    rw [ite_eq_left hequal, ← hequal]
    simpa only [hselfEquiv, ↓reduceIte] using hself
  · have hnoEquiv : ¬ Nonempty (rightRep.Equiv leftRep) := by
      rintro ⟨equivalence⟩
      exact hequal (Representation.char_iso equivalence).symm
    simpa only [hnoEquiv, hequal, ↓reduceIte] using horth

@[expose] noncomputable def characterDual {G : Type*} [Group G] [Fintype G]
    (character : G → ℂ) : Module.Dual ℂ (G → ℂ) :=
  (Nat.card G : ℂ)⁻¹ • ∑ element : G, character element⁻¹ • LinearMap.proj element

theorem characterDual_apply {G : Type*} [Group G] [Fintype G]
    (character value : G → ℂ) :
    characterDual character value =
      (Nat.card G : ℂ)⁻¹ * ∑ element : G, value element * character element⁻¹ := by
  simp only [characterDual, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.proj_apply,
    smul_eq_mul, mul_comm]

theorem irr_linearIndependent (G : Type*) [Group G] [Finite G] :
    LinearIndependent ℂ (fun character : BlocksIrr G => (character : G → ℂ)) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  apply LinearIndependent.of_pairwise_dual_eq_zero_one
    (fun character : BlocksIrr G => (character : G → ℂ))
    (fun character : BlocksIrr G => characterDual (character : G → ℂ))
  · intro left right hne
    rw [characterDual_apply]
    have hcharacters : (right : G → ℂ) ≠ (left : G → ℂ) := by
      intro hequal
      exact hne (Subtype.ext hequal.symm)
    simpa only [finsum_eq_sum_of_fintype, hcharacters, ↓reduceIte] using
      irr_orthogonality right.property left.property
  · intro character
    rw [characterDual_apply]
    simpa only [finsum_eq_sum_of_fintype, ↓reduceIte] using
      irr_orthogonality character.property character.property

theorem irr_finite (G : Type*) [Group G] [Finite G] : (BlocksIrr G).Finite := by
  let : Fintype G := Fintype.ofFinite G
  exact (irr_linearIndependent G).setFinite

theorem finiteOrder_trace_integral {space : Type*} [AddCommGroup space] [Module ℂ space]
    [FiniteDimensional ℂ space] (endomorphism : Module.End ℂ space) {exponent : ℕ}
    (hexponent : 0 < exponent) (hpow : endomorphism ^ exponent = 1) :
    IsIntegral ℤ (LinearMap.trace ℂ space endomorphism) := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  apply IsIntegral.multiset_sum
  intro root hroot
  have heigen : endomorphism.HasEigenvalue root :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly endomorphism root).mpr
      (Polynomial.mem_roots'.mp hroot).2
  have heigenPow := heigen.pow exponent
  rw [hpow] at heigenPow
  obtain ⟨vector, hvector⟩ := heigenPow.exists_hasEigenvector
  have hrootPow : root ^ exponent = 1 := by
    have hequation := hvector.apply_eq_smul
    have hvectorNe := hvector.2
    change vector = (root ^ exponent) • vector at hequation
    have hcancel : (1 : ℂ) • vector = (root ^ exponent) • vector := by
      simpa only [one_smul] using hequation
    exact ((smul_left_inj hvectorNe).mp hcancel).symm
  apply IsIntegral.of_pow hexponent
  rw [hrootPow]
  exact isIntegral_one

theorem irr_integral {G : Type*} [Group G] [Finite G] {character : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) (element : G) :
    IsIntegral ℤ (character element) := by
  obtain ⟨space, _, _, _, representation, _, rfl⟩ := hcharacter
  apply finiteOrder_trace_integral (representation element) (orderOf_pos element)
  rw [← map_pow, pow_orderOf_eq_one, map_one]

theorem irr_degree_ne_zero {G : Type*} [Group G] {character : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) : character 1 ≠ 0 := by
  obtain ⟨space, _, _, _, representation, hirreducible, rfl⟩ := hcharacter
  let : representation.IsIrreducible := hirreducible
  have : Nontrivial representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) representation.asModule
  have : Nontrivial space := representation.asModuleEquiv.symm.toEquiv.nontrivial
  rw [Representation.char_one]
  exact_mod_cast (Module.finrank_pos (R := ℂ) (M := space)).ne'

end CFSG.BrauerThirdMainTheorem.Helpers
