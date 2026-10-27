module

public import CFSG.FeitThompson.Local.InvariantComplementsInvertibleOrder
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.TensorProduct.Pi

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open TensorProduct

section Submodule

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  (L : Type*) [Field L] [Algebra k L]

theorem ker_baseChange_linearMap {W : Type*} [AddCommGroup W] [Module k W] (f : V →ₗ[k] W) :
    LinearMap.ker (f.baseChange L) = (LinearMap.ker f).baseChange L :=
  Module.Flat.ker_lTensor_eq L L f

theorem finrank_baseChange_submodule (p : Submodule k V) :
    Module.finrank L (p.baseChange L) = Module.finrank k p := by
  rw [← (Submodule.toBaseChange.toLinearEquiv L p).finrank_eq, Module.finrank_baseChange]

end Submodule

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

def baseChange (A : Type*) [CommSemiring A] [Algebra k A] (ρ : Representation k G V) :
    Representation A G (A ⊗[k] V) :=
  (Module.End.baseChangeHom k A V).toRingHom.toMonoidHom.comp ρ

variable (L : Type*) [Field L] [Algebra k L] (ρ : Representation k G V)

omit [Group G] [AddCommGroup V] [Module k V] in
theorem natCard_ne_zero_of_baseField (hG : (Nat.card G : k) ≠ 0) : (Nat.card G : L) ≠ 0 := by
  intro hc
  refine hG ?_
  have h3 : algebraMap k L ((Nat.card G : k)) = 0 := by simpa using hc
  exact (map_eq_zero_iff _ (algebraMap k L).injective).mp h3

theorem baseChange_apply (g : G) :
    (baseChange L ρ g : L ⊗[k] V →ₗ[L] L ⊗[k] V) = LinearMap.baseChange L (ρ g) := (rfl)

@[simp] theorem baseChange_apply_tmul (g : G) (a : L) (v : V) :
    baseChange L ρ g (a ⊗ₜ[k] v) = a ⊗ₜ[k] ρ g v := by
  rw [baseChange_apply]; simp

theorem baseChange_comp {H : Type*} [Group H] (f : H →* G) :
    baseChange L (ρ.comp f) = (baseChange L ρ).comp f := (rfl)

theorem ker_baseChange : (baseChange L ρ).ker = ρ.ker := by
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    ext v
    have := congrArg (fun F : Module.End L (L ⊗[k] V) => F ((1 : L) ⊗ₜ[k] v)) h
    simp only [baseChange_apply_tmul, Module.End.one_apply] at this
    exact Module.Flat.tensorProduct_mk_injective k V L this
  · intro h
    rw [baseChange_apply, h, LinearMap.baseChange_one]

theorem injective_baseChange_iff :
    Function.Injective (baseChange L ρ) ↔ Function.Injective ρ := by
  rw [← MonoidHom.ker_eq_bot_iff, ← MonoidHom.ker_eq_bot_iff, ker_baseChange]

private theorem invariants_eq_ker_pi :
    ρ.invariants = LinearMap.ker (LinearMap.pi fun g : G => ρ g - LinearMap.id) := by
  ext v
  simp [Representation.mem_invariants, LinearMap.mem_ker, funext_iff, sub_eq_zero]

theorem invariants_baseChange [Finite G] :
    (baseChange L ρ).invariants = ρ.invariants.baseChange L := by
  classical
  cases nonempty_fintype G
  have key : (TensorProduct.piRight k L L fun _ : G => V).toLinearMap ∘ₗ
        LinearMap.baseChange L (LinearMap.pi fun g : G => ρ g - LinearMap.id) =
      LinearMap.pi fun g : G => (baseChange L ρ g : L ⊗[k] V →ₗ[L] L ⊗[k] V) - LinearMap.id := by
    ext a v
    simp [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, baseChange_apply,
      TensorProduct.tmul_sub]
  rw [invariants_eq_ker_pi, invariants_eq_ker_pi, ← ker_baseChange_linearMap, ← key,
    LinearEquiv.ker_comp]

theorem finrank_invariants_baseChange [Finite G] :
    Module.finrank L (baseChange L ρ).invariants = Module.finrank k ρ.invariants := by
  rw [invariants_baseChange, finrank_baseChange_submodule]

theorem finrank_invariants_baseChange_restrict [Finite G] (A : Subgroup G) :
    Module.finrank L (Representation.invariants ((baseChange L ρ).comp A.subtype))
      = Module.finrank k (Representation.invariants (ρ.comp A.subtype)) := by
  rw [← baseChange_comp, finrank_invariants_baseChange]

theorem isSemisimpleRepresentation_baseChange [Finite G] (hG : (Nat.card G : k) ≠ 0) :
    (baseChange L ρ).IsSemisimpleRepresentation := by
  have : NeZero ((Nat.card G : L)) := ⟨natCard_ne_zero_of_baseField (G := G) L hG⟩
  infer_instance

theorem exists_invariant_isCompl_baseChange [Finite G] (hG : (Nat.card G : k) ≠ 0)
    (W : Submodule L (L ⊗[k] V)) (hW : ∀ g : G, ∀ v ∈ W, baseChange L ρ g v ∈ W) :
    ∃ U : Submodule L (L ⊗[k] V), (∀ g : G, ∀ v ∈ U, baseChange L ρ g v ∈ U) ∧ IsCompl W U :=
  exists_invariant_isCompl_of_natCard_ne_zero (natCard_ne_zero_of_baseField (L := L) hG)
    (baseChange L ρ) W hW

end Representation

section PrimeField

variable (p : ℕ) [Fact p.Prime]

theorem exists_isAlgClosed_extension_zmod :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod p) L), IsAlgClosed L :=
  ⟨AlgebraicClosure (ZMod p), inferInstance, inferInstance, inferInstance⟩

theorem isAlgebraic_algebraicClosure_zmod :
    Algebra.IsAlgebraic (ZMod p) (AlgebraicClosure (ZMod p)) := inferInstance

open CFSG.FeitThompson.Representation in
theorem baseChange_algebraicClosure_zmod_spec {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] (ρ : Representation (ZMod p) G V) :
    (baseChange (AlgebraicClosure (ZMod p)) ρ).ker = ρ.ker ∧
    (∀ A : Subgroup G,
      Module.finrank (AlgebraicClosure (ZMod p))
          (Representation.invariants
            ((baseChange (AlgebraicClosure (ZMod p)) ρ).comp A.subtype))
        = Module.finrank (ZMod p) (Representation.invariants (ρ.comp A.subtype))) ∧
    ((Nat.card G : ZMod p) ≠ 0 →
      (baseChange (AlgebraicClosure (ZMod p)) ρ).IsSemisimpleRepresentation) :=
  ⟨ker_baseChange _ ρ, fun A => finrank_invariants_baseChange_restrict _ ρ A,
    fun hG => isSemisimpleRepresentation_baseChange _ ρ hG⟩

end PrimeField

end CFSG.FeitThompson
