module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module Polynomial

namespace CFSG.FeitThompson

section Field

variable {k A V : Type*} [Field k] [Monoid A] [AddCommGroup V] [Module k V]

theorem nontrivial_of_isIrreducible (ρ : Representation k A V) [ρ.IsIrreducible] :
    Nontrivial V :=
  (Submodule.nontrivial_iff k).mp
    (nontrivial_of_ne _ _ (Subrepresentation.toSubmodule_injective.ne
      (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)))

theorem mem_adjoin_singleton_iff_exists_aeval (T S : Module.End k V) :
    S ∈ Algebra.adjoin k ({T} : Set (Module.End k V)) ↔ ∃ f : k[X], aeval T f = S := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact Iff.rfl

theorem coe_algebraMap_adjoin (T : Module.End k V) (c : k) :
    ((algebraMap k (Algebra.adjoin k ({T} : Set (Module.End k V))) c :
      Algebra.adjoin k ({T} : Set (Module.End k V))) : Module.End k V)
        = c • (1 : Module.End k V) := by
  simp [Algebra.algebraMap_eq_smul_one]

theorem adjoin_smul_def (T : Module.End k V)
    (S : Algebra.adjoin k ({T} : Set (Module.End k V))) (v : V) :
    S • v = (S : Module.End k V) v := (rfl)

theorem commute_of_mem_adjoin {ρ : Representation k A V} {T : Module.End k V}
    (hT : ∀ a, Commute (ρ a) T) {S : Module.End k V}
    (hS : S ∈ Algebra.adjoin k ({T} : Set (Module.End k V))) (a : A) : Commute (ρ a) S :=
  Algebra.commute_of_mem_adjoin_singleton_of_commute hS (hT a)

def intertwiningMapOfCommute {ρ : Representation k A V} {S : Module.End k V}
    (hS : ∀ a, Commute (ρ a) S) : ρ.IntertwiningMap ρ where
  toLinearMap := S
  isIntertwining' a := by
    ext v
    exact congrArg (fun g : Module.End k V => g v) (hS a).symm.eq

@[simp]
theorem intertwiningMapOfCommute_apply {ρ : Representation k A V} {S : Module.End k V}
    (hS : ∀ a, Commute (ρ a) S) (v : V) : intertwiningMapOfCommute hS v = S v := (rfl)

theorem injective_of_mem_adjoin_of_ne_zero {ρ : Representation k A V} [ρ.IsIrreducible]
    {T : Module.End k V} (hT : ∀ a, Commute (ρ a) T) {S : Module.End k V}
    (hS : S ∈ Algebra.adjoin k ({T} : Set (Module.End k V))) (hS0 : S ≠ 0) :
    Function.Injective S := by
  rcases Representation.IsIrreducible.injective_or_eq_zero
      (intertwiningMapOfCommute (commute_of_mem_adjoin hT hS)) with h | h
  · exact h
  · exact absurd (by ext v; exact congrArg (fun g : ρ.IntertwiningMap ρ => g v) h) hS0

theorem noZeroDivisors_adjoin {ρ : Representation k A V} [ρ.IsIrreducible]
    {T : Module.End k V} (hT : ∀ a, Commute (ρ a) T) :
    NoZeroDivisors (Algebra.adjoin k ({T} : Set (Module.End k V))) where
  eq_zero_or_eq_zero_of_mul_eq_zero {S S'} h := by
    by_cases hS : S = 0
    · exact Or.inl hS
    · refine Or.inr ?_
      have hinj := injective_of_mem_adjoin_of_ne_zero hT S.2
        (by simpa [Subalgebra.coe_eq_zero] using hS)
      have hcoe : (S : Module.End k V) * (S' : Module.End k V) = 0 := by
        simpa using congrArg Subtype.val h
      rw [← Subalgebra.coe_eq_zero]
      ext v
      have : (S : Module.End k V) ((S' : Module.End k V) v) = (S : Module.End k V) 0 := by
        simpa using congrArg (fun f : Module.End k V => f v) hcoe
      simpa using hinj this

theorem isDomain_adjoin {ρ : Representation k A V} [ρ.IsIrreducible]
    {T : Module.End k V} (hT : ∀ a, Commute (ρ a) T) :
    IsDomain (Algebra.adjoin k ({T} : Set (Module.End k V))) :=
  have := nontrivial_of_isIrreducible ρ
  have := noZeroDivisors_adjoin hT
  NoZeroDivisors.to_isDomain _

theorem isField_adjoin [FiniteDimensional k V] {ρ : Representation k A V} [ρ.IsIrreducible]
    {T : Module.End k V} (hT : ∀ a, Commute (ρ a) T) :
    IsField (Algebra.adjoin k ({T} : Set (Module.End k V))) :=
  have := isDomain_adjoin hT
  IsField.of_isDomain_of_finite k _

@[expose, instance_reducible]
noncomputable def genField [FiniteDimensional k V] {ρ : Representation k A V} [ρ.IsIrreducible]
    {T : Module.End k V} (hT : ∀ a, Commute (ρ a) T) :
    Field (Algebra.adjoin k ({T} : Set (Module.End k V))) :=
  (isField_adjoin hT).toField

theorem algebraMap_adjoin_injective {ρ : Representation k A V} [ρ.IsIrreducible]
    (T : Module.End k V) :
    Function.Injective (algebraMap k (Algebra.adjoin k ({T} : Set (Module.End k V)))) :=
  have := nontrivial_of_isIrreducible ρ
  RingHom.injective _

theorem finite_adjoin [Finite k] [FiniteDimensional k V] (T : Module.End k V) :
    Finite (Algebra.adjoin k ({T} : Set (Module.End k V))) :=
  have : Finite (Module.End k V) := Module.finite_of_finite k
  inferInstance

theorem finite_module_adjoin [FiniteDimensional k V] (T : Module.End k V) :
    Module.Finite (Algebra.adjoin k ({T} : Set (Module.End k V))) V :=
  Module.Finite.of_restrictScalars_finite k _ V

def genRepresentation (ρ : Representation k A V) {T : Module.End k V}
    (hT : ∀ a, Commute (ρ a) T) :
    Representation (Algebra.adjoin k ({T} : Set (Module.End k V))) A V where
  toFun a :=
    { toFun := ρ a
      map_add' := map_add _
      map_smul' := fun S v => by
        change (ρ a) ((S : Module.End k V) v) = (S : Module.End k V) ((ρ a) v)
        exact congrArg (fun g : Module.End k V => g v) (commute_of_mem_adjoin hT S.2 a).eq }
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

@[simp]
theorem genRepresentation_apply (ρ : Representation k A V) {T : Module.End k V}
    (hT : ∀ a, Commute (ρ a) T) (a : A) (v : V) :
    genRepresentation ρ hT a v = ρ a v := (rfl)

theorem isSimpleOrder_subrepresentation_genRepresentation (ρ : Representation k A V)
    [ρ.IsIrreducible] {T : Module.End k V} (hT : ∀ a, Commute (ρ a) T) :
    IsSimpleOrder (Subrepresentation (genRepresentation ρ hT)) := by
  have hV := nontrivial_of_isIrreducible ρ
  have : Nontrivial (Subrepresentation (genRepresentation ρ hT)) :=
    nontrivial_of_ne ⊥ ⊤ fun h =>
      (bot_ne_top (α := Submodule (Algebra.adjoin k ({T} : Set (Module.End k V))) V))
        (Subrepresentation.ext_iff.mp h)
  refine ⟨fun W => ?_⟩
  let W' : Subrepresentation ρ :=
    ⟨W.toSubmodule.restrictScalars k, fun a v hv => W.apply_mem_toSubmodule a hv⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top W' with h | h
  · exact Or.inl (Subrepresentation.ext ((Submodule.restrictScalars_eq_bot_iff _ _ _).mp
      (congrArg Subrepresentation.toSubmodule h)))
  · exact Or.inr (Subrepresentation.ext ((Submodule.restrictScalars_eq_top_iff _ _ _).mp
      (congrArg Subrepresentation.toSubmodule h)))

theorem isIrreducible_genRepresentation [FiniteDimensional k V] (ρ : Representation k A V)
    [ρ.IsIrreducible] {T : Module.End k V} (hT : ∀ a, Commute (ρ a) T) :
    letI := genField hT
    (genRepresentation ρ hT).IsIrreducible :=
  isSimpleOrder_subrepresentation_genRepresentation ρ hT

end Field

section ZMod

variable {p : ℕ} [Fact p.Prime] {A V : Type*} [Monoid A] [AddCommGroup V] [Module (ZMod p) V]

theorem exists_natCard_adjoin_eq_pow [Nontrivial V] [FiniteDimensional (ZMod p) V]
    (T : Module.End (ZMod p) V) :
    ∃ s : ℕ, 1 ≤ s ∧
      Nat.card (Algebra.adjoin (ZMod p) ({T} : Set (Module.End (ZMod p) V))) = p ^ s :=
  have : Finite (Module.End (ZMod p) V) := Module.finite_of_finite (ZMod p)
  ⟨finrank (ZMod p) (Algebra.adjoin (ZMod p) ({T} : Set (Module.End (ZMod p) V))),
    Module.finrank_pos, (FiniteField.pow_finrank_eq_natCard p _).symm⟩

theorem exists_natCard_adjoin_eq_pow_of_isIrreducible [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p) A V) [ρ.IsIrreducible] (T : Module.End (ZMod p) V)
    (_hT : ∀ a, Commute (ρ a) T) :
    ∃ s : ℕ, 1 ≤ s ∧
      Nat.card (Algebra.adjoin (ZMod p) ({T} : Set (Module.End (ZMod p) V))) = p ^ s :=
  have := nontrivial_of_isIrreducible ρ
  exists_natCard_adjoin_eq_pow T

end ZMod

end CFSG.FeitThompson
