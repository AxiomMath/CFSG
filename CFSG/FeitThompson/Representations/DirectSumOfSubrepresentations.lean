module

public import CFSG.FeitThompson.Representations.HomogeneousCyclicQuotientIrreducible
import CFSG.FeitThompson.Representations.ComplexCompleteReducibility
import Mathlib.RepresentationTheory.Maschke

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Representation

variable {k : Type*} [Field k] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module k V]

def equivOfComp {G' : Type*} [Group G'] {W : Type*} [AddCommGroup W] [Module k W]
    (f : G' →* G) (hf : Function.Surjective f) {ρ : Representation k G V}
    {σ : Representation k G W} (e : Representation.Equiv (ρ.comp f) (σ.comp f)) : ρ.Equiv σ :=
  Representation.Equiv.mk e.toLinearEquiv fun g => by
    obtain ⟨g', rfl⟩ := hf g
    exact LinearMap.ext fun v =>
      Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g' v

@[simp]
theorem coe_equivOfComp {G' : Type*} [Group G'] {W : Type*} [AddCommGroup W] [Module k W]
    (f : G' →* G) (hf : Function.Surjective f) {ρ : Representation k G V}
    {σ : Representation k G W} (e : Representation.Equiv (ρ.comp f) (σ.comp f)) (v : V) :
    equivOfComp f hf e v = e v := (rfl)

noncomputable def directSumEquivCongr {ι : Type*} [DecidableEq ι] {M N : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] [∀ i, AddCommGroup (N i)]
    [∀ i, Module k (N i)] {ρs : ∀ i, Representation k G (M i)}
    {σs : ∀ i, Representation k G (N i)} (F : ∀ i, (ρs i).Equiv (σs i)) :
    (Representation.directSum ρs).Equiv (Representation.directSum σs) :=
  Representation.Equiv.mk (DirectSum.congrLinearEquiv fun i => (F i).toLinearEquiv) fun g => by
    refine DirectSum.linearMap_ext k fun i => LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Representation.directSum_apply, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
    congr 1
    exact Representation.IntertwiningMap.isIntertwining _ _ (F i).toIntertwiningMap g x

@[simp]
theorem directSumEquivCongr_apply_apply {ι : Type*} [DecidableEq ι] {M N : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] [∀ i, AddCommGroup (N i)]
    [∀ i, Module k (N i)] {ρs : ∀ i, Representation k G (M i)}
    {σs : ∀ i, Representation k G (N i)} (F : ∀ i, (ρs i).Equiv (σs i))
    (x : DirectSum ι M) (i : ι) : directSumEquivCongr F x i = F i (x i) := by
  change (DirectSum.congrLinearEquiv fun i => (F i).toLinearEquiv) x i = _
  simp [DirectSum.coe_congrLinearEquiv]

noncomputable def equivOfIsInternal {ρ : Representation k G V} {ι : Type*} [DecidableEq ι]
    (σ : ι → Subrepresentation ρ)
    (h : Function.Bijective (DirectSum.coeLinearMap fun i => (σ i).toSubmodule)) :
    (Representation.directSum fun i => (σ i).toRepresentation).Equiv ρ :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i => (σ i).toSubmodule) h)
    fun g => by
      refine DirectSum.linearMap_ext k fun i => LinearMap.ext fun x => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        Representation.directSum_apply, LinearEquiv.ofBijective_apply, DirectSum.lmap_lof]
      rw [DirectSum.lof_eq_of, DirectSum.coeLinearMap_of, DirectSum.lof_eq_of,
        DirectSum.coeLinearMap_of]
      rfl

@[simp]
theorem coe_equivOfIsInternal {ρ : Representation k G V} {ι : Type*} [DecidableEq ι]
    (σ : ι → Subrepresentation ρ)
    (h : Function.Bijective (DirectSum.coeLinearMap fun i => (σ i).toSubmodule))
    (x : DirectSum ι fun i => ((σ i).toSubmodule : Type _)) :
    equivOfIsInternal σ h x = DirectSum.coeLinearMap (fun i => (σ i).toSubmodule) x := (rfl)

theorem exists_bijective_coeLinearMap_isIrreducible [Finite G] [FiniteDimensional k V]
    (hG : (Nat.card G : k) ≠ 0) (ρ : Representation k G V) :
    ∃ (n : ℕ) (σ : Fin n → Subrepresentation ρ),
      Function.Bijective (DirectSum.coeLinearMap fun i => (σ i).toSubmodule) ∧
        ∀ i, (σ i).toRepresentation.IsIrreducible := by
  classical
  have _ : Module.Finite (MonoidAlgebra k G) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k _ _
  have : NeZero ((Nat.card G : k)) := ⟨hG⟩
  have hss : IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule := inferInstance
  have hatoms : sSup {a : Submodule (MonoidAlgebra k G) ρ.asModule | IsAtom a} = ⊤ := by
    simpa [isSimpleModule_iff_isAtom.symm] using
      @IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra k G) _ ρ.asModule _ _ hss
  obtain ⟨s, hind, hsup, hat⟩ := exists_sSupIndep_of_sSup_atoms_eq_top hatoms
  have h1 : iSupIndep ((↑) : s → Submodule (MonoidAlgebra k G) ρ.asModule) :=
    (sSupIndep_iff s).1 hind
  have hfin : Finite s := by
    have h2 := Submodule.finite_ne_bot_of_iSupIndep h1
    have heq : {i : s | (i : Submodule (MonoidAlgebra k G) ρ.asModule) ≠ ⊥} = Set.univ := by
      ext i; simp [(hat i.2).1]
    rw [heq] at h2
    exact Set.finite_univ_iff.1 h2
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  have hInternal : DirectSum.IsInternal
      fun i : Fin n => (e.symm i : Submodule (MonoidAlgebra k G) ρ.asModule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (h1.comp e.symm.injective) <| by
      rw [← hsup, sSup_eq_iSup']
      exact e.symm.iSup_comp (g := fun i : s => (i : Submodule (MonoidAlgebra k G) ρ.asModule))
  refine ⟨n, fun i => Subrepresentation.ofSubmodule' (e.symm i), hInternal, fun i => ?_⟩
  rw [← isAtom_iff_isIrreducible]
  have h3 := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).isAtom_iff
    (Subrepresentation.ofSubmodule' (e.symm i : Submodule (MonoidAlgebra k G) ρ.asModule))
  rw [Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
    show (Subrepresentation.ofSubmodule'
        (e.symm i : Submodule (MonoidAlgebra k G) ρ.asModule)).asSubmodule
      = (e.symm i : Submodule (MonoidAlgebra k G) ρ.asModule) from
      Submodule.toSubMulAction_inj.mp rfl] at h3
  exact h3.1 (hat (e.symm i).2)

theorem isIrreducible_comp_of_homogeneous_of_isCyclic_quotient {M P : Type*} [AddCommGroup M]
    [Module k M] [Group P] [IsAlgClosed k] [FiniteDimensional k V] {m : ℕ}
    {ρ : Representation k G V} {σ : Representation k P M} (f : P →* G)
    (hf : Function.Injective f) [f.range.Normal] [IsCyclic (G ⧸ f.range)]
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (e : Representation.Equiv (ρ.comp f) (Representation.directSum fun _ : Fin m => σ)) :
    Representation.IsIrreducible (ρ.comp f) := by
  set ε : P ≃* f.range := MonoidHom.ofInjective hf with hε
  have hsub : f.range.subtype.comp ε.toMonoidHom = f :=
    MonoidHom.ext fun x => MonoidHom.ofInjective_apply hf
  set σ' : Representation k f.range M := σ.comp ε.symm.toMonoidHom with hσ'def
  have hσ' : σ'.IsIrreducible := Representation.isIrreducible_comp hσ _ ε.symm.surjective
  have hcomp : σ'.comp ε.toMonoidHom = σ := MonoidHom.ext fun g => by simp [hσ'def]
  have hρcomp : (ρ.comp f.range.subtype).comp ε.toMonoidHom = ρ.comp f := by
    rw [MonoidHom.comp_assoc, hsub]
  have e' : Representation.Equiv ((ρ.comp f.range.subtype).comp ε.toMonoidHom)
      ((Representation.directSum fun _ : Fin m => σ').comp ε.toMonoidHom) := by
    rw [hρcomp, show (Representation.directSum fun _ : Fin m => σ').comp ε.toMonoidHom
      = Representation.directSum fun _ : Fin m => σ'.comp ε.toMonoidHom from rfl, hcomp]
    exact e
  have hN := isIrreducible_comp_subtype_of_homogeneous_of_isCyclic_quotient hρ hσ'
    (equivOfComp ε.toMonoidHom ε.surjective e')
  have := Representation.isIrreducible_comp hN ε.toMonoidHom ε.surjective
  rwa [hρcomp] at this

end

end CFSG.FeitThompson
