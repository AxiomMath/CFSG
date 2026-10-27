module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import CFSG.LinearAlgebra.CoprimeActions.SmallDimensionStableType
public import CFSG.GroupTheory.CoprimeActionSupport.FiniteOrderIntertwinerNormalize

public section

open Submodule

open scoped MonoidAlgebra

open Module

namespace CFSG.LinearAlgebra.CoprimeActions.SmallDimensionStableIrreducibleImage

open CFSG.LinearAlgebra.CoprimeActions.PrimeNormalizerStableIrreducibleType

section aux

variable {F : Type*} [Field F] {E : Type*} [Group E]
  {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

private def intertwiners (η : Representation F E W) (σ : Representation F E V) :
    Submodule F (W →ₗ[F] V) where
  carrier := {f | ∀ e w, f (η e w) = σ e (f w)}
  add_mem' := by
    intro f g hf hg e w
    simp [hf e w, hg e w]
  zero_mem' := by intro e w; simp
  smul_mem' := by
    intro c f hf e w
    simp [hf e w]

private theorem exists_inj_intertwiner [IsAlgClosed F] [FiniteDimensional F V] [FiniteDimensional F W]
    [Nontrivial W]
    (η : Representation F E W) (hη : η.IsIrreducible) (σ : Representation F E V)
    (α : MulAut E) (r : ℕ) (hr : 0 < r) (hα : α ^ r = 1)
    (U : W ≃ₗ[F] W) (hUr : U ^ r = 1) (T : V ≃ₗ[F] V) (hTr : T ^ r = 1)
    (hU : ∀ e w, U (η e w) = η (α e) (U w))
    (hT : ∀ e v, T (σ e v) = σ (α e) (T v))
    (f0 : W →ₗ[F] V) (hf0 : f0 ≠ 0) (hf0i : ∀ e w, f0 (η e w) = σ e (f0 w)) :
    ∃ f : W →ₗ[F] V, Function.Injective f ∧ (∀ e w, f (η e w) = σ e (f w)) ∧
      LinearMap.range f ≤ (LinearMap.range f).comap (T : V →ₗ[F] V) := by
  let I := intertwiners η σ
  let L : (W →ₗ[F] V) →ₗ[F] (W →ₗ[F] V) :=
    { toFun := fun f => (T : V →ₗ[F] V) ∘ₗ f ∘ₗ (U.symm : W →ₗ[F] W)
      map_add' := by intro f g; ext w; simp
      map_smul' := by intro c f; ext w; simp }
  have hL : ∀ f ∈ I, L f ∈ I := by
    intro f hf e w
    have hUinv : ∀ e w, U.symm (η e w) = η (α⁻¹ e) (U.symm w) := by
      intro e w
      apply U.injective
      rw [hU, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      simp
    have hf' : ∀ e w, f (η e w) = σ e (f w) := hf
    show T (f (U.symm (η e w))) = σ e (T (f (U.symm w)))
    rw [hUinv, hf', hT]
    simp
  let L' : End F I := L.restrict hL
  haveI : Nontrivial I := by
    refine ⟨⟨f0, hf0i⟩, 0, ?_⟩
    intro h
    exact hf0 (congrArg Subtype.val h)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue L'
  obtain ⟨⟨f, hfI⟩, hfe⟩ := hμ.exists_hasEigenvector
  have hfne : f ≠ 0 := fun h => hfe.2 (Subtype.ext h)
  have hfeq : ∀ w, T (f (U.symm w)) = μ • f w := by
    intro w
    have := congrArg (fun g : I => (g : W →ₗ[F] V) w) (Module.End.mem_eigenspace_iff.1 hfe.1)
    simpa [L', L] using this
  have hfi : ∀ e w, f (η e w) = σ e (f w) := hfI
  have hTf : ∀ w, T (f w) = μ • f (U w) := by
    intro w
    simpa using hfeq (U w)
  have hinj : Function.Injective f := by
    let K : Subrepresentation η :=
      ⟨LinearMap.ker f, by
        intro e w hw
        have : f w = 0 := hw
        show f (η e w) = 0
        rw [hfi, this]; simp⟩
    rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
    · rw [← LinearMap.ker_eq_bot]
      have := congrArg Subrepresentation.toSubmodule h
      exact this
    · exfalso
      apply hfne
      ext w
      have : w ∈ K := by rw [h]; trivial
      exact this
  refine ⟨f, hinj, hfi, ?_⟩
  rintro _ ⟨w, rfl⟩
  exact ⟨μ • U w, by simp [hTf]⟩

end aux

section spec

variable {F : Type*} [Field F] {E : Type*} [Group E] {V : Type*} [AddCommGroup V] [Module F V]

theorem caseA' {F : Type*} [Field F]
    {E : Type*} [Group E]
    {V : Type*} [AddCommGroup V] [Module F V]
    (σ : Representation F E V)
    (α : MulAut E)
    (T : V ≃ₗ[F] V)
    (hcov : ∀ e v, T (σ e v) = σ (α e) (T v))
    (S0 : Submodule F[E] σ.asModule) [IsSimpleModule F[E] S0]
    (ψ : S0 ≃ₗ[F[E]] tw (mkSLEquiv σ α T hcov) S0) :
    ∃ W : Submodule F V, ∃ hW : ∀ e, W ≤ W.comap (σ e), Nontrivial W ∧
      Nonempty ((Representation.subrepresentation σ W hW).asModule ≃ₗ[F[E]] S0) ∧
      ∃ U : W ≃ₗ[F] W, ∀ e w,
        U (Representation.subrepresentation σ W hW e w) =
          Representation.subrepresentation σ W hW (α e) (U w) := by
  set T' := mkSLEquiv σ α T hcov with hT'
  let aE := σ.asModuleEquiv
  let W : Submodule F V := (S0.restrictScalars F).comap aE.symm.toLinearMap
  have hmemW : ∀ v, v ∈ W ↔ aE.symm v ∈ S0 := fun v => Iff.rfl
  have hW : ∀ e, W ≤ W.comap (σ e) := by
    intro e v hv
    rw [Submodule.mem_comap, hmemW, Representation.asModuleEquiv_symm_map_rho]
    exact S0.smul_mem _ ((hmemW v).1 hv)
  let e0 : W ≃ₗ[F] S0 :=
    { toFun := fun w => ⟨aE.symm w, (hmemW _).1 w.2⟩
      invFun := fun s => ⟨aE s, (hmemW _).2 (by simpa using s.2)⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp
      left_inv := fun w => by ext; simp
      right_inv := fun s => by ext; simp }
  have he0 : ∀ e (w : W), e0 (Representation.subrepresentation σ W hW e w) =
      MonoidAlgebra.of F E e • e0 w := by
    intro e w
    ext
    exact Representation.asModuleEquiv_symm_map_rho σ e (w : V)
  set ρ := Representation.subrepresentation σ W hW with hρ
  have he0alg : ∀ (r : F[E]) (w : W), e0 (Representation.asAlgebraHom ρ r w) = r • e0 w := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g =>
      intro w
      have : Representation.asAlgebraHom ρ (MonoidAlgebra.of F E g) w = ρ g w := by
        simp [MonoidAlgebra.of_apply]
      rw [this]; exact he0 g w
    | add x y hx hy => intro w; simp [map_add, hx, hy, add_smul]
    | smul c x hx => intro w; simp [hx, smul_assoc]
  haveI : Nontrivial S0 := IsSimpleModule.nontrivial F[E] S0
  haveI : Nontrivial W := e0.toEquiv.nontrivial
  let eN : ρ.asModule ≃ₗ[F[E]] S0 :=
    { toFun := fun x => e0 (ρ.asModuleEquiv x)
      invFun := fun s => ρ.asModuleEquiv.symm (e0.symm s)
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        simp only [Representation.asModuleEquiv_map_smul, RingHom.id_apply]
        exact he0alg r _
      left_inv := fun x => by simp
      right_inv := fun s => by simp }
  refine ⟨W, hW, inferInstance, ⟨eN⟩, ?_⟩
  · have hF : ∀ (c : F) (y : tw T' S0), ψ.symm (c • y) = c • ψ.symm y := by
      intro c y
      rw [← algebraMap_smul F[E] c y, map_smul, algebraMap_smul]
    have hTc : ∀ (c : F) (x : σ.asModule), T' (c • x) = c • T' x := by
      intro c x
      show σ.asModuleEquiv.symm (T (σ.asModuleEquiv (c • x))) = c • σ.asModuleEquiv.symm (T (σ.asModuleEquiv x))
      simp
    have hmT : ∀ s : S0, T' (s : σ.asModule) ∈ tw T' S0 := fun s => Submodule.mem_map_of_mem s.2
    have hmT' : ∀ y : tw T' S0, T'.symm (y : σ.asModule) ∈ S0 := fun y =>
      (Submodule.mem_map_equiv S0).1 y.2
    let UM : S0 ≃ₗ[F] S0 :=
      { toFun := fun s => ψ.symm ⟨T' (s : σ.asModule), hmT s⟩
        invFun := fun s => ⟨T'.symm (ψ s : σ.asModule), hmT' _⟩
        map_add' := fun x y => by
          rw [← map_add]; congr 1; ext; simp
        map_smul' := fun c x => by
          simp only [RingHom.id_apply]
          rw [← hF]; congr 1; ext; exact hTc c _
        left_inv := fun s => by
          ext; simp
        right_inv := fun s => by
          simp only [LinearEquiv.apply_symm_apply]
          ext; simp }
    have hUM : ∀ e (s : S0), UM (MonoidAlgebra.of F E e • s) =
        MonoidAlgebra.of F E (α e) • UM s := by
      intro e s
      show ψ.symm _ = _ • ψ.symm _
      rw [← map_smul]; congr 1; ext
      show T' (MonoidAlgebra.of F E e • (s : σ.asModule)) = MonoidAlgebra.of F E (α e) • T' s
      rw [map_smulₛₗ]
      simp [twRing, MonoidAlgebra.of_apply]
      rfl
    refine ⟨e0.trans (UM.trans e0.symm), fun e w => ?_⟩
    simp only [LinearEquiv.trans_apply]
    rw [he0, hUM]
    apply e0.injective
    rw [he0, e0.apply_symm_apply, e0.apply_symm_apply]

end spec

theorem exists_image {F : Type*} [Field F] [IsAlgClosed F]
    {E : Type*} [Group E] [Finite E]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (σ : Representation F E V) (hcard : (Nat.card E : F) ≠ 0)
    (α : MulAut E) (q : ℕ) [hq : Fact q.Prime] (hα : α ^ q = 1)
    (T : V ≃ₗ[F] V) (hT : T ^ q = 1)
    (hcov : ∀ e v, T (σ e v) = σ (α e) (T v))
    (hdim : Module.finrank F V < q)
    (S0 : Submodule F[E] σ.asModule) [IsSimpleModule F[E] S0] :
    ∃ W : Submodule F V, W ≠ ⊥ ∧ (∀ e, W ≤ W.comap (σ e)) ∧
      W ≤ W.comap (T : V →ₗ[F] V) ∧
      ∃ hW : ∀ e, W ≤ W.comap (σ e),
        (Representation.subrepresentation σ W hW).IsIrreducible ∧
        Nonempty ((Representation.subrepresentation σ W hW).asModule ≃ₗ[F[E]] S0) := by
  obtain ⟨ψ⟩ := CFSG.LinearAlgebra.CoprimeActions.SmallDimensionStableType.twist_iso σ hcard α T q hT
    hcov hdim S0
  obtain ⟨W0, hW0, hnt, ⟨eN⟩, U, hU⟩ := caseA' σ α T hcov S0 ψ
  set η := Representation.subrepresentation σ W0 hW0 with hη
  have hirr : η.IsIrreducible := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule]
    haveI : IsSimpleModule F[E] S0 := inferInstance
    exact IsSimpleModule.congr eN
  obtain ⟨U', hU'r, hU'⟩ := CFSG.GroupTheory.CoprimeActionSupport.FiniteOrderIntertwinerNormalize.exists_normalized
    η hirr α q hq.out.pos hα U hU
  obtain ⟨f, hinj, hfi, hfT⟩ := exists_inj_intertwiner η hirr σ α q hq.out.pos hα U' hU'r T hT
    hU' hcov W0.subtype (by
      intro h
      obtain ⟨w, hw⟩ := exists_ne (0 : W0)
      exact hw (by simpa using LinearMap.congr_fun h w)) (fun e w => rfl)
  have hS : ∀ e, LinearMap.range f ≤ (LinearMap.range f).comap (σ e) := by
    rintro e _ ⟨w, rfl⟩
    exact ⟨η e w, hfi e w⟩
  have hiso : Nonempty ((Representation.subrepresentation σ (LinearMap.range f) hS).asModule ≃ₗ[F[E]] S0) := by
    let fI : Representation.IntertwiningMap η (Representation.subrepresentation σ (LinearMap.range f) hS) :=
      { toLinearMap := f.rangeRestrict
        isIntertwining' := fun g => by
          ext w
          simpa using hfi g w }
    let g := Representation.IntertwiningMap.equivLinearMapAsModule _ _ fI
    have hg : Function.Bijective g := by
      constructor
      · intro x y hxy
        exact hinj (congrArg Subtype.val hxy)
      · intro y
        obtain ⟨w, hw⟩ := f.surjective_rangeRestrict y
        exact ⟨w, hw⟩
    exact ⟨(LinearEquiv.ofBijective g hg).symm.trans eN⟩
  haveI : Nontrivial W0 := hnt
  refine ⟨LinearMap.range f, ?_, hS, hfT, hS, ?_, hiso⟩
  · intro h
    rw [LinearMap.range_eq_bot] at h
    obtain ⟨w, hw⟩ := exists_ne (0 : W0)
    exact hw (hinj (by simpa using congrFun (congrArg DFunLike.coe h) w))
  · rw [Representation.irreducible_iff_isSimpleModule_asModule]
    obtain ⟨e⟩ := hiso
    exact IsSimpleModule.congr e

end CFSG.LinearAlgebra.CoprimeActions.SmallDimensionStableIrreducibleImage
