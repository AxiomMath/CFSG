module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Algebra.Field.ZMod

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

def linearGroupRep (A : Subgroup (V ≃ₗ[k] V)) : Representation k A V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp A.subtype

@[simp] lemma linearGroupRep_apply (A : Subgroup (V ≃ₗ[k] V)) (a : A) (v : V) :
    linearGroupRep A a v = (a : V ≃ₗ[k] V) v := (rfl)

theorem isIrreducible_linearGroupRep_iff {A : Subgroup (V ≃ₗ[k] V)} :
    (linearGroupRep A).IsIrreducible ↔
      Nontrivial V ∧ ∀ W : Submodule k V, (∀ a ∈ A, ∀ v ∈ W, a v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, fun W hW => ?_⟩
    · have h : (⊥ : Subrepresentation (linearGroupRep A)) ≠ ⊤ := bot_ne_top
      rw [Ne, Subrepresentation.ext_iff] at h
      exact (Submodule.nontrivial_iff k).mp ⟨⟨⊥, ⊤, h⟩⟩
    · exact (IsSimpleOrder.eq_bot_or_eq_top
        (⟨W, fun a v hv => hW a a.2 v hv⟩ : Subrepresentation (linearGroupRep A))).imp
        (congrArg Subrepresentation.toSubmodule) (congrArg Subrepresentation.toSubmodule)
  · rintro ⟨hV, hW⟩
    have hbt : (⊥ : Subrepresentation (linearGroupRep A)) ≠ ⊤ := by
      rw [Ne, Subrepresentation.ext_iff]
      exact ((Submodule.nontrivial_iff k).mpr hV).exists_pair_ne.elim fun _ _ => bot_ne_top
    have : Nontrivial (Subrepresentation (linearGroupRep A)) := ⟨⟨⊥, ⊤, hbt⟩⟩
    exact ⟨fun W => (hW W.toSubmodule fun a ha v hv => W.apply_mem_toSubmodule ⟨a, ha⟩ hv).imp
      Subrepresentation.ext Subrepresentation.ext⟩

theorem nontrivial_of_isIrreducible_linearGroupRep (A : Subgroup (V ≃ₗ[k] V))
    [(linearGroupRep A).IsIrreducible] : Nontrivial V :=
  ((isIrreducible_linearGroupRep_iff (A := A)).mp inferInstance).1

theorem eq_bot_or_eq_top_of_invariant (A : Subgroup (V ≃ₗ[k] V))
    [(linearGroupRep A).IsIrreducible] (W : Submodule k V)
    (hW : ∀ a ∈ A, ∀ v ∈ W, a v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  ((isIrreducible_linearGroupRep_iff (A := A)).mp inferInstance).2 W hW

variable {A : Subgroup (V ≃ₗ[k] V)}

def endSet (A : Subgroup (V ≃ₗ[k] V)) : Set (Module.End k V) :=
  LinearEquiv.toLinearMap '' (A : Set (V ≃ₗ[k] V))

lemma mem_endSet_iff {x : Module.End k V} :
    x ∈ endSet A ↔ ∃ a ∈ A, (a : Module.End k V) = x := by
  simp [endSet, Set.mem_image]

def envelopingSubalgebra (A : Subgroup (V ≃ₗ[k] V)) : Subalgebra k (Module.End k V) :=
  (Submodule.span k (endSet A)).toSubalgebra
    (Submodule.subset_span ⟨1, one_mem A, rfl⟩)
    (by
      intro x y hx hy
      have hmul : Submodule.span k (endSet A) * Submodule.span k (endSet A) ≤
          Submodule.span k (endSet A) := by
        rw [Submodule.span_mul_span]
        refine Submodule.span_le.2 ?_
        rintro z ⟨u, ⟨a, ha, rfl⟩, v, ⟨b, hb, rfl⟩, rfl⟩
        exact Submodule.subset_span ⟨a * b, mul_mem ha hb, rfl⟩
      exact hmul (Submodule.mul_mem_mul hx hy))

lemma toSubmodule_envelopingSubalgebra :
    Subalgebra.toSubmodule (envelopingSubalgebra A) = Submodule.span k (endSet A) :=
  Submodule.toSubalgebra_toSubmodule _ _ _

lemma mem_envelopingSubalgebra_iff {x : Module.End k V} :
    x ∈ envelopingSubalgebra A ↔ x ∈ Submodule.span k (endSet A) := Iff.rfl

lemma coe_mem_envelopingSubalgebra {a : V ≃ₗ[k] V} (ha : a ∈ A) :
    (a : Module.End k V) ∈ envelopingSubalgebra A :=
  Submodule.subset_span ⟨a, ha, rfl⟩

lemma injective_algebraMap_envelopingSubalgebra [Nontrivial V] :
    Function.Injective (algebraMap k ↥(envelopingSubalgebra A)) := by
  intro x y hxy
  refine FaithfulSMul.algebraMap_injective k (Module.End k V) ?_
  simpa using congrArg Subtype.val hxy

lemma mul_comm_of_mem_envelopingSubalgebra [IsMulCommutative A] {x y : Module.End k V}
    (hx : x ∈ envelopingSubalgebra A) (hy : y ∈ envelopingSubalgebra A) : x * y = y * x := by
  rw [mem_envelopingSubalgebra_iff] at hx hy
  have base : ∀ g ∈ endSet A, ∀ z ∈ Submodule.span k (endSet A), g * z = z * g := by
    rintro g ⟨a, ha, rfl⟩ z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨b, hb, rfl⟩ := mem_endSet_iff.mp hw
        exact congrArg LinearEquiv.toLinearMap (setLike_mul_comm ha hb)
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add, add_mul, hu, hv]
    | smul c u _ hu => rw [mul_smul_comm, smul_mul_assoc, hu]
  induction hx using Submodule.span_induction with
  | mem w hw => exact base w hw y hy
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul, mul_add, hu, hv]
  | smul c u _ hu => rw [smul_mul_assoc, mul_smul_comm, hu]

instance instCommRingEnvelopingSubalgebra [IsMulCommutative A] :
    CommRing ↥(envelopingSubalgebra A) :=
  { (inferInstance : Ring ↥(envelopingSubalgebra A)) with
    mul_comm := fun x y => Subtype.ext (mul_comm_of_mem_envelopingSubalgebra x.2 y.2) }

instance instModuleFiniteEnvelopingSubalgebra [FiniteDimensional k V] :
    Module.Finite k ↥(envelopingSubalgebra A) :=
  Module.Finite.of_injective (envelopingSubalgebra A).val.toLinearMap Subtype.val_injective

theorem injective_of_mem_envelopingSubalgebra [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] {x : Module.End k V} (hx : x ∈ envelopingSubalgebra A)
    (hx0 : x ≠ 0) : Function.Injective x := by
  have hker : LinearMap.ker x = ⊥ ∨ LinearMap.ker x = ⊤ := by
    refine eq_bot_or_eq_top_of_invariant A _ fun a ha v hv => ?_
    have hcomm : (a : Module.End k V) * x = x * (a : Module.End k V) :=
      mul_comm_of_mem_envelopingSubalgebra (coe_mem_envelopingSubalgebra ha) hx
    have hax : x (a v) = a (x v) := by
      simpa using congrArg (fun f : Module.End k V => f v) hcomm.symm
    simp only [LinearMap.mem_ker] at hv ⊢
    rw [hax, hv, map_zero]
  rcases hker with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exact absurd (LinearMap.ker_eq_top.mp h) hx0

instance instNontrivialEnvelopingSubalgebra [(linearGroupRep A).IsIrreducible] :
    Nontrivial ↥(envelopingSubalgebra A) :=
  have : Nontrivial V := nontrivial_of_isIrreducible_linearGroupRep A
  inferInstance

instance instNoZeroDivisorsEnvelopingSubalgebra [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] : NoZeroDivisors ↥(envelopingSubalgebra A) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro x y hxy
    by_cases hx : x = 0
    · exact Or.inl hx
    refine Or.inr ?_
    have hx0 : (x : Module.End k V) ≠ 0 := fun h => hx (Subtype.ext h)
    have hinj := injective_of_mem_envelopingSubalgebra x.2 hx0
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    have hv : (x : Module.End k V) ((y : Module.End k V) v) = (x : Module.End k V) 0 := by
      simpa using congrArg (fun f : Module.End k V => f v) (congrArg Subtype.val hxy)
    simpa using hinj hv

theorem isField_envelopingSubalgebra [IsMulCommutative A] [(linearGroupRep A).IsIrreducible]
    [FiniteDimensional k V] : IsField ↥(envelopingSubalgebra A) :=
  have : IsDomain ↥(envelopingSubalgebra A) := IsDomain.mk
  IsField.of_isDomain_of_finite k _

noncomputable instance instFieldEnvelopingSubalgebra [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] [FiniteDimensional k V] :
    Field ↥(envelopingSubalgebra A) :=
  isField_envelopingSubalgebra.toField

def evalEnvelopingSubalgebra (A : Subgroup (V ≃ₗ[k] V)) (s : V) :
    ↥(envelopingSubalgebra A) →ₗ[k] V :=
  (LinearMap.applyₗ s).comp (envelopingSubalgebra A).val.toLinearMap

@[simp] lemma evalEnvelopingSubalgebra_apply (s : V) (x : ↥(envelopingSubalgebra A)) :
    evalEnvelopingSubalgebra A s x = (x : Module.End k V) s := (rfl)

theorem injective_evalEnvelopingSubalgebra [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] {s : V} (hs : s ≠ 0) :
    Function.Injective (evalEnvelopingSubalgebra A s) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  simp only [LinearMap.mem_ker, evalEnvelopingSubalgebra_apply] at hx
  by_contra hx0
  have h0 : (x : Module.End k V) ≠ 0 := fun h => hx0 (Subtype.ext h)
  exact hs (injective_of_mem_envelopingSubalgebra x.2 h0 (a₁ := s) (a₂ := 0) (by simpa using hx))

theorem surjective_evalEnvelopingSubalgebra [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] {s : V} (hs : s ≠ 0) :
    Function.Surjective (evalEnvelopingSubalgebra A s) := by
  have hrange : LinearMap.range (evalEnvelopingSubalgebra A s) = ⊥ ∨
      LinearMap.range (evalEnvelopingSubalgebra A s) = ⊤ := by
    refine eq_bot_or_eq_top_of_invariant A _ fun a ha v hv => ?_
    obtain ⟨x, rfl⟩ := hv
    exact ⟨⟨(a : Module.End k V) * (x : Module.End k V),
      mul_mem (coe_mem_envelopingSubalgebra ha) x.2⟩, by simp⟩
  rcases hrange with h | h
  · exfalso
    have hmem : s ∈ LinearMap.range (evalEnvelopingSubalgebra A s) := ⟨1, by simp⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hs hmem
  · exact LinearMap.range_eq_top.mp h

noncomputable def evalEnvelopingSubalgebraEquiv [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] {s : V} (hs : s ≠ 0) :
    ↥(envelopingSubalgebra A) ≃ₗ[k] V :=
  LinearEquiv.ofBijective (evalEnvelopingSubalgebra A s)
    ⟨injective_evalEnvelopingSubalgebra hs, surjective_evalEnvelopingSubalgebra hs⟩

@[simp] lemma evalEnvelopingSubalgebraEquiv_apply [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] {s : V} (hs : s ≠ 0) (x : ↥(envelopingSubalgebra A)) :
    evalEnvelopingSubalgebraEquiv hs x = (x : Module.End k V) s := (rfl)

theorem finrank_envelopingSubalgebra [IsMulCommutative A] [(linearGroupRep A).IsIrreducible] :
    finrank k ↥(envelopingSubalgebra A) = finrank k V := by
  have : Nontrivial V := nontrivial_of_isIrreducible_linearGroupRep A
  obtain ⟨s, hs⟩ := exists_ne (0 : V)
  exact (evalEnvelopingSubalgebraEquiv (A := A) hs).finrank_eq

theorem natCard_envelopingSubalgebra [IsMulCommutative A] [(linearGroupRep A).IsIrreducible]
    [FiniteDimensional k V] :
    Nat.card ↥(envelopingSubalgebra A) = Nat.card k ^ finrank k V := by
  rw [Module.natCard_eq_pow_finrank (K := k) (V := ↥(envelopingSubalgebra A)),
    finrank_envelopingSubalgebra]

theorem natCard_envelopingSubalgebra_zmod {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {A : Subgroup (V ≃ₗ[ZMod p] V)} [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] [FiniteDimensional (ZMod p) V] :
    Nat.card ↥(envelopingSubalgebra A) = p ^ finrank (ZMod p) V := by
  rw [natCard_envelopingSubalgebra, Nat.card_zmod]

theorem finrank_eq_one_over_envelopingSubalgebra [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] [FiniteDimensional k V] :
    finrank ↥(envelopingSubalgebra A) V = 1 := by
  have : Nontrivial V := nontrivial_of_isIrreducible_linearGroupRep A
  obtain ⟨s, hs⟩ := exists_ne (0 : V)
  rw [finrank_eq_one_iff_of_nonzero s hs, Submodule.span_singleton_eq_top_iff]
  intro v
  obtain ⟨x, hx⟩ := surjective_evalEnvelopingSubalgebra (A := A) hs v
  exact ⟨x, hx⟩

def unitsHom (A : Subgroup (V ≃ₗ[k] V)) : A →* (↥(envelopingSubalgebra A))ˣ where
  toFun a :=
    { val := ⟨((a : V ≃ₗ[k] V) : Module.End k V), coe_mem_envelopingSubalgebra a.2⟩
      inv := ⟨(((a : V ≃ₗ[k] V).symm : V ≃ₗ[k] V) : Module.End k V),
        coe_mem_envelopingSubalgebra (inv_mem a.2)⟩
      val_inv := Subtype.ext (LinearMap.ext fun v => by simp)
      inv_val := Subtype.ext (LinearMap.ext fun v => by simp) }
  map_one' := Units.ext (Subtype.ext (LinearMap.ext fun _ => rfl))
  map_mul' _ _ := Units.ext (Subtype.ext (LinearMap.ext fun _ => rfl))

@[simp] lemma coe_unitsHom (a : A) :
    (((unitsHom A a : ↥(envelopingSubalgebra A)) : Module.End k V)) =
      ((a : V ≃ₗ[k] V) : Module.End k V) := (rfl)

lemma injective_unitsHom : Function.Injective (unitsHom A) := by
  intro a b hab
  have h : ((unitsHom A a : ↥(envelopingSubalgebra A)) : Module.End k V) =
      ((unitsHom A b : ↥(envelopingSubalgebra A)) : Module.End k V) := by rw [hab]
  simp only [coe_unitsHom] at h
  exact Subtype.ext (LinearEquiv.toLinearMap_injective h)

end

end CFSG.FeitThompson
