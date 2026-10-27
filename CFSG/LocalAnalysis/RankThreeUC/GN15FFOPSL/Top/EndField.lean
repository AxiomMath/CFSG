module

public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
public import CFSG.LieType.SpecialLinear.BorelStd
public import CFSG.LieType.SpecialLinear.Stage.TrivialType

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open Matrix Module Representation MonoidAlgebra
open CFSG.HardMathSupport.GuralnickMalle
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LieType.SpecialLinear
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.Quasithin.SmithCurtis
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MonoidAlgebra TensorProduct

section Instances

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (ρ : Representation (ZMod 2) G W) [IsIrreducible ρ]

instance finiteAsModule : Finite ρ.asModule := finite_asModule ρ

instance endFieldCharP : CharP (End (ZMod 2)[G] ρ.asModule) 2 := endField_charP ρ 2

noncomputable instance endFieldFintype : Fintype (End (ZMod 2)[G] ρ.asModule) :=
  Fintype.ofFinite _

instance finiteDimensionalEndField :
    FiniteDimensional (End (ZMod 2)[G] ρ.asModule) ρ.asModule :=
  finiteDimensional_endField ρ

end Instances

section Transport

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G W)

@[expose] noncomputable def transportEnd (a : W →ₗ[ZMod 2] W) :
    ρ.asModule →ₗ[ZMod 2] ρ.asModule :=
  (ρ.asModuleEquiv.symm : ρ.asModule ≃ₗ[ZMod 2] W).toLinearMap ∘ₗ a ∘ₗ
    (ρ.asModuleEquiv : ρ.asModule ≃ₗ[ZMod 2] W).toLinearMap

@[simp] theorem transportEnd_apply (a : W →ₗ[ZMod 2] W) (x : ρ.asModule) :
    transportEnd ρ a x = ρ.asModuleEquiv.symm (a (ρ.asModuleEquiv x)) := rfl

theorem transportEnd_smul (a : W →ₗ[ZMod 2] W)
    (ha : ∀ f : W →ₗ[ZMod 2] W, (∀ g, f ∘ₗ ρ g = ρ g ∘ₗ f) → a ∘ₗ f = f ∘ₗ a)
    (c : End (ZMod 2)[G] ρ.asModule) (x : ρ.asModule) :
    transportEnd ρ a (c • x) = c • transportEnd ρ a x := by
  classical
  have hsingle : ∀ (g : G) (y : ρ.asModule),
      (single g (1 : ZMod 2) : (ZMod 2)[G]) • y = endFieldRep ρ g y := by
    intro g y
    apply ρ.asModuleEquiv.injective
    rw [Representation.asModuleEquiv_map_smul, endFieldRep_apply']
    simp
  have hcG : ∀ (g : G) (y : ρ.asModule), c (endFieldRep ρ g y) = endFieldRep ρ g (c y) := by
    intro g y
    calc c (endFieldRep ρ g y) = c ((single g (1 : ZMod 2) : (ZMod 2)[G]) • y) := by
          rw [hsingle]
      _ = (single g (1 : ZMod 2) : (ZMod 2)[G]) • c y := c.map_smul _ _
      _ = endFieldRep ρ g (c y) := hsingle g (c y)
  let f : W →ₗ[ZMod 2] W :=
    (ρ.asModuleEquiv : ρ.asModule ≃ₗ[ZMod 2] W).toLinearMap ∘ₗ c ∘ₗ
      (ρ.asModuleEquiv.symm : ρ.asModule ≃ₗ[ZMod 2] W).toLinearMap
  have hf : ∀ g : G, f ∘ₗ ρ g = ρ g ∘ₗ f := by
    intro g
    ext w
    change ρ.asModuleEquiv (c (ρ.asModuleEquiv.symm (ρ g w))) =
      ρ g (ρ.asModuleEquiv (c (ρ.asModuleEquiv.symm w)))
    have hw : ρ.asModuleEquiv.symm (ρ g w) =
        endFieldRep ρ g (ρ.asModuleEquiv.symm w) := by
      rw [endFieldRep_apply, LinearEquiv.apply_symm_apply]
    rw [hw, hcG, endFieldRep_apply']
  apply ρ.asModuleEquiv.injective
  calc ρ.asModuleEquiv (transportEnd ρ a (c • x))
      = a (ρ.asModuleEquiv (c • x)) := by simp [transportEnd_apply]
    _ = a (f (ρ.asModuleEquiv x)) := by
        simp [f]
    _ = f (a (ρ.asModuleEquiv x)) := by
        have h := congrArg (fun l : W →ₗ[ZMod 2] W => l (ρ.asModuleEquiv x)) (ha f hf)
        simpa [LinearMap.comp_apply] using h
    _ = ρ.asModuleEquiv (c • transportEnd ρ a x) := by
        simp [f, transportEnd_apply]

end Transport

section TopActor

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G W)

@[expose] noncomputable def topActor (D : Subgroup (W ≃ₗ[ZMod 2] W)) :
    Representation (ZMod 2) ↥D ρ.asModule where
  toFun d := transportEnd ρ ((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)
  map_one' := by
    apply LinearMap.ext
    intro x
    simp [transportEnd_apply]
  map_mul' d e := by
    apply LinearMap.ext
    intro x
    rw [show ((d * e : ↥D) : W ≃ₗ[ZMod 2] W) =
        (d : W ≃ₗ[ZMod 2] W) * (e : W ≃ₗ[ZMod 2] W) from rfl,
      LinearEquiv.coe_toLinearMap_mul]
    simp [transportEnd_apply]

@[simp] theorem topActor_apply (D : Subgroup (W ≃ₗ[ZMod 2] W)) (d : ↥D) (x : ρ.asModule) :
    topActor ρ D d x = transportEnd ρ ((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) x := rfl

theorem topActor_smul (D : Subgroup (W ≃ₗ[ZMod 2] W))
    (hcomm : ∀ d ∈ D, ∀ f : W →ₗ[ZMod 2] W,
      (∀ g, f ∘ₗ ρ g = ρ g ∘ₗ f) →
      ((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) ∘ₗ f =
        f ∘ₗ ((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W))
    (d : ↥D) (c : End (ZMod 2)[G] ρ.asModule) (x : ρ.asModule) :
    topActor ρ D d (c • x) = c • topActor ρ D d x :=
  transportEnd_smul ρ _ (hcomm d d.2) c x

theorem topActor_mul_self (D : Subgroup (W ≃ₗ[ZMod 2] W))
    (hD2W : ∀ d ∈ D, d * d = 1) (d : ↥D) :
    topActor ρ D d * topActor ρ D d = 1 := by
  rw [← map_mul, show d * d = 1 from Subtype.ext (hD2W d d.2), map_one]

theorem topActor_isPGroup (D : Subgroup (W ≃ₗ[ZMod 2] W))
    (hD2W : ∀ d ∈ D, d * d = 1) : IsPGroup 2 ↥D := by
  refine IsPGroup.of_exponent_dvd_pow (n := 1) ?_
  rw [pow_one]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one fun d => by
    have hd : d * d = 1 := Subtype.ext (hD2W d d.2)
    simpa [pow_two] using hd

theorem topActor_quadratic (D : Subgroup (W ≃ₗ[ZMod 2] W))
    (hquadW : ∀ a ∈ D, ∀ b ∈ D, ∀ w,
      ((b : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)
        (((a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) w - w) =
      ((a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) w - w)
    (a b : ↥D) (x : ρ.asModule) :
    topActor ρ D b (topActor ρ D a x - x) = topActor ρ D a x - x := by
  have h := hquadW a a.2 b b.2 (ρ.asModuleEquiv x)
  have hx : ρ.asModuleEquiv (topActor ρ D a x - x) =
      ((a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (ρ.asModuleEquiv x) -
        ρ.asModuleEquiv x := by
    simp [topActor_apply, transportEnd_apply]
  calc topActor ρ D b (topActor ρ D a x - x)
      = ρ.asModuleEquiv.symm (((b : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)
          (ρ.asModuleEquiv (topActor ρ D a x - x))) := by
        simp [topActor_apply, transportEnd_apply]
    _ = ρ.asModuleEquiv.symm (((b : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)
          (((a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (ρ.asModuleEquiv x) -
            ρ.asModuleEquiv x)) := by rw [hx]
    _ = ρ.asModuleEquiv.symm (((a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)
          (ρ.asModuleEquiv x) - ρ.asModuleEquiv x) := by rw [h]
    _ = topActor ρ D a x - x := by
        simp [topActor_apply, transportEnd_apply]

end TopActor

section Compat

variable {n : ℕ} {F : Type} [Field F]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin n) F) W)
  (D : Subgroup (W ≃ₗ[ZMod 2] W))

theorem topActor_compat
    (hcompatW : ∀ d ∈ D, ∃ B : GL (Fin n) F, IsUpperGL B ∧
      ∃ (τ : F ≃+* F) (ε : ℕ), ∀ g w,
        ((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (ρ g w) =
          ρ (borelStd n F B τ ε g) (((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) w))
    (d : ↥D) :
    ∃ A : GL (Fin n) F, IsUpperGL A ∧ ∃ (τ : F ≃+* F) (ε : ℕ),
      ∀ g x, topActor ρ D d (endFieldRep ρ g x) =
        endFieldRep ρ (borelStd n F A τ ε g) (topActor ρ D d x) := by
  obtain ⟨A, hA, τ, ε, h⟩ := hcompatW d d.2
  refine ⟨A, hA, τ, ε, fun g x => ?_⟩
  change ρ.asModuleEquiv.symm
      (((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (ρ g (ρ.asModuleEquiv x))) =
    ρ.asModuleEquiv.symm
      (ρ (borelStd n F A τ ε g)
        (((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (ρ.asModuleEquiv x)))
  rw [h g (ρ.asModuleEquiv x)]

end Compat

section Hered

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G W)
  (D : Subgroup (W ≃ₗ[ZMod 2] W))
  (δW : Representation (ZMod 2) ↥D W)

theorem topActor_isOffenderOn
    (hδW : ∀ d w, δW d w = ((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) w)
    (hD2W : ∀ d ∈ D, d * d = 1)
    (heredW : ∀ Z : Submodule (ZMod 2) W,
      (∀ d : ↥D, ∀ z ∈ Z, ((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) z ∈ Z) →
      IsOffenderOn δW ⊤ Z)
    (Z : Submodule (ZMod 2) ρ.asModule)
    (hZ : ∀ d : ↥D, ∀ z ∈ Z, topActor ρ D d z ∈ Z) :
    IsOffenderOn (topActor ρ D) ⊤ Z := by
  classical
  let Z' : Submodule (ZMod 2) W := Z.map (ρ.asModuleEquiv : ρ.asModule →ₗ[ZMod 2] W)
  have hZ' : ∀ d : ↥D, ∀ z ∈ Z',
      ((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) z ∈ Z' := by
    intro d z hz
    obtain ⟨z0, hz0, rfl⟩ := Submodule.mem_map.mp hz
    exact Submodule.mem_map.mpr ⟨topActor ρ D d z0, hZ d z0 hz0, by
      simp [topActor_apply, transportEnd_apply]⟩
  have hoffW : IsOffenderOn δW ⊤ Z' := heredW Z' hZ'
  have hcen : cenOn (topActor ρ D) ⊤ Z = cenOn δW ⊤ Z' := by
    ext d
    constructor
    · rintro ⟨-, hd⟩
      refine ⟨trivial, ?_⟩
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
      rw [hδW]
      simpa [topActor_apply, transportEnd_apply] using congrArg ρ.asModuleEquiv (hd z hz)
    · rintro ⟨-, hd⟩
      refine ⟨trivial, ?_⟩
      intro z hz
      apply ρ.asModuleEquiv.injective
      change ρ.asModuleEquiv (ρ.asModuleEquiv.symm
          (((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (ρ.asModuleEquiv z))) =
        ρ.asModuleEquiv z
      rw [LinearEquiv.apply_symm_apply, ← hδW]
      exact hd (ρ.asModuleEquiv z) (Submodule.mem_map_of_mem hz)
  have hfixSub : (RankThree.FFModules.fixSub (topActor ρ D) ⊤).map
        (ρ.asModuleEquiv : ρ.asModule →ₗ[ZMod 2] W) =
      RankThree.FFModules.fixSub δW ⊤ := by
    apply Submodule.ext
    intro w
    constructor
    · rintro ⟨v, hv, rfl⟩
      intro d hd
      rw [hδW]
      simpa [topActor_apply, transportEnd_apply] using
        congrArg ρ.asModuleEquiv (hv d (Subgroup.mem_top d))
    · intro hw
      refine ⟨ρ.asModuleEquiv.symm w, ?_, by simp⟩
      intro d hd
      rw [topActor_apply, transportEnd_apply, LinearEquiv.apply_symm_apply, ← hδW,
        hw d hd]
  have hfix : (fixOn (topActor ρ D) ⊤ Z).map
        (ρ.asModuleEquiv : ρ.asModule →ₗ[ZMod 2] W) = fixOn δW ⊤ Z' := by
    rw [fixOn, fixOn, Submodule.map_inf _ ρ.asModuleEquiv.injective, hfixSub]
  have hcardZ : Nat.card Z = Nat.card Z' :=
    Nat.card_congr (LinearEquiv.ofSubmodules
      (ρ.asModuleEquiv : ρ.asModule ≃ₗ[ZMod 2] W) Z Z' rfl).toEquiv
  have hcardFix : Nat.card (fixOn (topActor ρ D) ⊤ Z) =
      Nat.card (fixOn δW ⊤ Z') :=
    Nat.card_congr (LinearEquiv.ofSubmodules
      (ρ.asModuleEquiv : ρ.asModule ≃ₗ[ZMod 2] W)
      (fixOn (topActor ρ D) ⊤ Z) (fixOn δW ⊤ Z') hfix).toEquiv
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    constructor
    · intro u hu
      have ha2 : a * a = 1 := Subtype.ext (hD2W a a.2)
      have hb2 : b * b = 1 := Subtype.ext (hD2W b b.2)
      have hab : (a * b) * (a * b) = 1 :=
        Subtype.ext (hD2W (a * b) (D.mul_mem a.2 b.2))
      have hc1 : a * b * a⁻¹ * b⁻¹ = 1 := by
        rw [show a⁻¹ = a from inv_eq_of_mul_eq_one_right ha2,
          show b⁻¹ = b from inv_eq_of_mul_eq_one_right hb2]
        simpa [mul_assoc] using hab
      rw [hc1, map_one, Module.End.one_apply]
    · intro u hu
      rw [show a * a = 1 from Subtype.ext (hD2W a a.2), map_one, Module.End.one_apply]
  · rw [hcardZ, hcen, hcardFix]
    exact hoffW.2

end Hered

section TopType

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin (n + 1)) F) W) [IsIrreducible ρ]

omit [Fintype F] [CharP F 2] in
theorem top_isSimpleRep :
    IsSimpleRep (CFSG.Theory.Representation.extendScalars
      (AlgebraicClosure (End (ZMod 2)[SpecialLinearGroup (Fin (n + 1)) F] ρ.asModule))
      (endFieldRep ρ)) :=
  isSimpleRep_extendScalars_endFieldRep ρ _

theorem top_exists_type (hne : ∃ g, ρ g ≠ 1) :
    ∃ y : (AlgebraicClosure (End (ZMod 2)[SpecialLinearGroup (Fin (n + 1)) F] ρ.asModule)) ⊗[
        End (ZMod 2)[SpecialLinearGroup (Fin (n + 1)) F] ρ.asModule] ρ.asModule,
      ∃ χ : SpecialLinearGroup (Fin (n + 1)) F →
        AlgebraicClosure (End (ZMod 2)[SpecialLinearGroup (Fin (n + 1)) F] ρ.asModule),
      ∃ J : Finset (Fin n),
        IsCoverType (rankOne n F 2)
          (CFSG.Theory.Representation.extendScalars
            (AlgebraicClosure (End (ZMod 2)[SpecialLinearGroup (Fin (n + 1)) F] ρ.asModule))
            (endFieldRep ρ)) y χ J ∧
        ∃ s, s ∉ J := by
  classical
  let E := End (ZMod 2)[SpecialLinearGroup (Fin (n + 1)) F] ρ.asModule
  let k := AlgebraicClosure E
  let : Algebra F k :=
    (nonempty_ringHom_algebraicClosure (K := E) (F₀ := F) (p := 2)).some.toAlgebra
  have hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (endFieldRep ρ)) :=
    top_isSimpleRep ρ
  obtain ⟨y, χ, J, ht⟩ :=
    CFSG.LieType.SpecialLinear.exists_isCoverType_sl (m := n) (F := F) (p := 2) (k := k)
      (V := k ⊗[E] ρ.asModule) hsimp
  have hne' : ∃ g, CFSG.Theory.Representation.extendScalars k (endFieldRep ρ) g ≠ 1 := by
    obtain ⟨g, hg⟩ := hne
    refine ⟨g, fun h => hg ?_⟩
    rwa [CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.extendScalars_endFieldRep_eq_one_iff
      ρ k g] at h
  obtain ⟨s, hs⟩ :=
    CFSG.LieType.SpecialLinear.exists_not_mem_of_isCoverType hsimp ht hne'
  exact ⟨y, χ, J, ht, s, hs⟩

end TopType

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
