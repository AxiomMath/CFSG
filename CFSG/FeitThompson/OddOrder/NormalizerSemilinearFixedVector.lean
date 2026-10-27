module

public import CFSG.FeitThompson.OddOrder.AbelianIrreducibleEnvelopingField
public import Mathlib.RepresentationTheory.Invariants

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {A B : Subgroup (V ≃ₗ[k] V)}

lemma mem_invariants_linearGroupRep_iff {v : V} :
    v ∈ Representation.invariants (linearGroupRep B) ↔ ∀ b ∈ B, b v = v := by
  simp [Representation.mem_invariants, Subtype.forall]

lemma conjAlgEquiv_coe (b a : V ≃ₗ[k] V) :
    (b.conjAlgEquiv k) ((a : Module.End k V)) = ((b * a * b⁻¹ : V ≃ₗ[k] V) : Module.End k V) := by
  ext v; simp [LinearEquiv.conjAlgEquiv_apply_apply]

lemma conj_mem_of_mem_normalizer {b a : V ≃ₗ[k] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) (ha : a ∈ A) : b * a * b⁻¹ ∈ A :=
  (Subgroup.mem_normalizer_iff.mp hb a).mp ha

lemma conj_mem_envelopingSubalgebra {b : V ≃ₗ[k] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) {x : Module.End k V}
    (hx : x ∈ envelopingSubalgebra A) :
    (b.conjAlgEquiv k) x ∈ envelopingSubalgebra A := by
  rw [mem_envelopingSubalgebra_iff] at hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨a, ha, rfl⟩ := mem_endSet_iff.mp hw
      rw [conjAlgEquiv_coe]
      exact coe_mem_envelopingSubalgebra (conj_mem_of_mem_normalizer hb ha)
  | zero => simp
  | add u v _ _ hu hv => simpa using add_mem hu hv
  | smul c u _ hu => simpa using Subalgebra.smul_mem _ hu c

private def conjEnvelopingAux (A : Subgroup (V ≃ₗ[k] V)) {b : V ≃ₗ[k] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) :
    ↥(envelopingSubalgebra A) →ₐ[k] ↥(envelopingSubalgebra A) :=
  AlgHom.codRestrict ((b.conjAlgEquiv k).toAlgHom.comp (envelopingSubalgebra A).val) _
    (fun x => conj_mem_envelopingSubalgebra hb x.2)

@[simp] private lemma coe_conjEnvelopingAux {b : V ≃ₗ[k] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) (x : ↥(envelopingSubalgebra A)) :
    ((conjEnvelopingAux A hb x : Module.End k V)) = (b.conjAlgEquiv k) x := (rfl)

def conjEnveloping (A : Subgroup (V ≃ₗ[k] V)) {b : V ≃ₗ[k] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) :
    ↥(envelopingSubalgebra A) ≃ₐ[k] ↥(envelopingSubalgebra A) :=
  AlgEquiv.ofAlgHom (conjEnvelopingAux A hb) (conjEnvelopingAux A (inv_mem hb))
    (AlgHom.ext fun x => Subtype.ext (by
      ext v
      simp [LinearEquiv.conjAlgEquiv_apply_apply, show (b⁻¹ : V ≃ₗ[k] V) = b.symm from rfl]))
    (AlgHom.ext fun x => Subtype.ext (by
      ext v
      simp [LinearEquiv.conjAlgEquiv_apply_apply, show (b⁻¹ : V ≃ₗ[k] V) = b.symm from rfl]))

@[simp] lemma coe_conjEnveloping_apply {b : V ≃ₗ[k] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) (x : ↥(envelopingSubalgebra A)) :
    ((conjEnveloping A hb x : Module.End k V)) = (b.conjAlgEquiv k) x := (rfl)

lemma conjEnveloping_apply_apply {b : V ≃ₗ[k] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) (x : ↥(envelopingSubalgebra A)) (v : V) :
    (conjEnveloping A hb x : Module.End k V) v = b ((x : Module.End k V) (b.symm v)) := by
  simp [LinearEquiv.conjAlgEquiv_apply_apply]

@[simp] lemma conjEnveloping_algebraMap {b : V ≃ₗ[k] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) (c : k) :
    conjEnveloping A hb (algebraMap k ↥(envelopingSubalgebra A) c) =
      algebraMap k ↥(envelopingSubalgebra A) c :=
  AlgEquiv.commutes _ c

lemma conjEnveloping_coe_group {b a : V ≃ₗ[k] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) (ha : a ∈ A) :
    conjEnveloping A hb ⟨(a : Module.End k V), coe_mem_envelopingSubalgebra ha⟩ =
      ⟨((b * a * b⁻¹ : V ≃ₗ[k] V) : Module.End k V),
        coe_mem_envelopingSubalgebra (conj_mem_of_mem_normalizer hb ha)⟩ :=
  Subtype.ext (by simpa using conjAlgEquiv_coe b a)

def conjEnvelopingHom (A : Subgroup (V ≃ₗ[k] V)) :
    ↥(Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) →*
      (↥(envelopingSubalgebra A) ≃ₐ[k] ↥(envelopingSubalgebra A)) where
  toFun b := conjEnveloping A b.2
  map_one' := AlgEquiv.ext fun x => Subtype.ext (LinearMap.ext fun v => by
    rw [conjEnveloping_apply_apply]; rfl)
  map_mul' b c := AlgEquiv.ext fun x => Subtype.ext (LinearMap.ext fun v => by
    rw [conjEnveloping_apply_apply]
    change _ = (conjEnveloping A b.2 (conjEnveloping A c.2 x) : Module.End k V) v
    rw [conjEnveloping_apply_apply, conjEnveloping_apply_apply]
    rfl)

@[simp] lemma conjEnvelopingHom_apply (b : ↥(Subgroup.normalizer (A : Set (V ≃ₗ[k] V)))) :
    conjEnvelopingHom A b = conjEnveloping A b.2 := (rfl)

noncomputable def conjEnvelopingHomOfLE (hBA : B ≤ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) :
    B →* (↥(envelopingSubalgebra A) ≃ₐ[k] ↥(envelopingSubalgebra A)) :=
  (conjEnvelopingHom A).comp (Subgroup.inclusion hBA)

@[simp] lemma conjEnvelopingHomOfLE_apply (hBA : B ≤ Subgroup.normalizer (A : Set (V ≃ₗ[k] V)))
    (b : B) : conjEnvelopingHomOfLE hBA b = conjEnveloping A (hBA b.2) := (rfl)

lemma conjEnveloping_apply_apply_of_fixed {b : V ≃ₗ[k] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) {s : V} (hs : b s = s)
    (x : ↥(envelopingSubalgebra A)) :
    (conjEnveloping A hb x : Module.End k V) s = b ((x : Module.End k V) s) := by
  rw [conjEnveloping_apply_apply, (LinearEquiv.symm_apply_eq b).mpr hs.symm]

variable [IsMulCommutative A] [(linearGroupRep A).IsIrreducible]

theorem evalEnvelopingSubalgebraEquiv_conjEnveloping {s : V} (hs0 : s ≠ 0)
    {b : V ≃ₗ[k] V} (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) (hbs : b s = s)
    (x : ↥(envelopingSubalgebra A)) :
    evalEnvelopingSubalgebraEquiv (A := A) hs0 (conjEnveloping A hb x) =
      b (evalEnvelopingSubalgebraEquiv hs0 x) := by
  rw [evalEnvelopingSubalgebraEquiv_apply, evalEnvelopingSubalgebraEquiv_apply,
    conjEnveloping_apply_apply_of_fixed hb hbs]

theorem symm_evalEnvelopingSubalgebraEquiv_apply {s : V} (hs0 : s ≠ 0)
    {b : V ≃ₗ[k] V} (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) (hbs : b s = s)
    (v : V) :
    (evalEnvelopingSubalgebraEquiv (A := A) hs0).symm (b v) =
      conjEnveloping A hb ((evalEnvelopingSubalgebraEquiv hs0).symm v) := by
  apply (evalEnvelopingSubalgebraEquiv (A := A) hs0).injective
  rw [LinearEquiv.apply_symm_apply, evalEnvelopingSubalgebraEquiv_conjEnveloping hs0 hb hbs,
    LinearEquiv.apply_symm_apply]

theorem injective_conjEnvelopingHomOfLE
    (hBA : B ≤ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) {s : V} (hs0 : s ≠ 0)
    (hs : s ∈ Representation.invariants (linearGroupRep B)) :
    Function.Injective (conjEnvelopingHomOfLE (A := A) hBA) := by
  rw [mem_invariants_linearGroupRep_iff] at hs
  rw [injective_iff_map_eq_one]
  intro b hb
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨x, rfl⟩ := surjective_evalEnvelopingSubalgebra (A := A) hs0 v
  rw [evalEnvelopingSubalgebra_apply, ← conjEnveloping_apply_apply_of_fixed (hBA b.2) (hs b b.2) x,
    ← conjEnvelopingHomOfLE_apply hBA b, hb]
  simp

end

end CFSG.FeitThompson
