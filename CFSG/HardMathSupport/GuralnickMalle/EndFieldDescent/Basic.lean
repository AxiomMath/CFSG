module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
public import CFSG.Walter.Bender1970.S1.FixedPointFreeBaseChange
public import CFSG.HardMathSupport.GuralnickMalle.BasicGeneral

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open Representation
open scoped MonoidAlgebra TensorProduct

section FixSubGen

variable {K : Type*} [Field K] {H : Type*} [Group H] {W : Type*} [AddCommGroup W] [Module K W]

theorem fixSubGen_eq_invariants (σ : Representation K H W) (A : Subgroup H) :
    fixSubGen σ A = Representation.invariants (σ.comp A.subtype) := by
  ext w
  simp [fixSubGen, Representation.mem_invariants]

end FixSubGen

variable {F : Type*} [Field F] [Finite F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] (ρ : Representation F G V) [IsIrreducible ρ]

omit [Finite F] [FiniteDimensional F V] [ρ.IsIrreducible] in
theorem finite_asModule [Finite V] : Finite ρ.asModule :=
  Finite.of_injective ρ.asModuleEquiv ρ.asModuleEquiv.injective

theorem finiteDimensional_endField [Finite V] :
    FiniteDimensional (End F[G] ρ.asModule) ρ.asModule :=
  Module.finite_iff_finite.mpr (finite_asModule ρ)

section Cardinality

variable {A : Subgroup G}

def fixSubGenEquiv : fixSubGen ρ A ≃ fixSubGen (endFieldRep ρ) A where
  toFun v := ⟨ρ.asModuleEquiv.symm v.1, by
    intro a ha
    have hv : ρ a v.1 = v.1 := v.2 a ha
    simp [endFieldRep_apply, hv]⟩
  invFun w := ⟨ρ.asModuleEquiv w.1, by
    intro a ha
    have hw : endFieldRep ρ a w.1 = w.1 := w.2 a ha
    have hthis := congrArg ρ.asModuleEquiv hw
    rw [endFieldRep_apply, LinearEquiv.apply_symm_apply] at hthis
    exact hthis⟩
  left_inv v := by ext; simp
  right_inv w := by ext; simp

theorem card_fixSubGen_endField :
    Nat.card (fixSubGen ρ A) = Nat.card (End F[G] ρ.asModule) ^
      finrank (End F[G] ρ.asModule) (fixSubGen (endFieldRep ρ) A) := by
  classical
  let K := End F[G] ρ.asModule
  have : Finite V := Module.finite_iff_finite.mp ‹FiniteDimensional F V›
  have : Finite ρ.asModule := finite_asModule ρ
  have : Module.Finite K (fixSubGen (endFieldRep ρ) A) :=
    Module.finite_iff_finite.mpr Subtype.finite
  calc Nat.card (fixSubGen ρ A) = Nat.card (fixSubGen (endFieldRep ρ) A) :=
        Nat.card_congr (fixSubGenEquiv ρ)
    _ = Nat.card K ^ finrank K (fixSubGen (endFieldRep ρ) A) :=
        Module.natCard_eq_pow_finrank

theorem card_eq_pow_finrank_endField :
    Nat.card V = Nat.card (End F[G] ρ.asModule) ^
      finrank (End F[G] ρ.asModule) ρ.asModule := by
  classical
  let K := End F[G] ρ.asModule
  have : Finite V := Module.finite_iff_finite.mp ‹FiniteDimensional F V›
  have : Finite ρ.asModule := finite_asModule ρ
  have : Module.Finite K ρ.asModule := Module.finite_iff_finite.mpr ‹Finite ρ.asModule›
  calc Nat.card V = Nat.card ρ.asModule := (Nat.card_congr ρ.asModuleEquiv.toEquiv).symm
    _ = Nat.card K ^ finrank K ρ.asModule := Module.natCard_eq_pow_finrank

end Cardinality

section ExtendScalars

variable [Finite G]

omit [Finite G] in
theorem extendScalars_isIrreducible (k : Type*) [Field k]
    [Algebra (End F[G] ρ.asModule) k] :
    IsIrreducible (Theory.Representation.extendScalars k (endFieldRep ρ)) := by
  have : Finite V := Module.finite_iff_finite.mp ‹FiniteDimensional F V›
  have : FiniteDimensional (End F[G] ρ.asModule) ρ.asModule :=
    finiteDimensional_endField ρ
  have : Theory.Representation.IsAbsolutelyIrreducible (endFieldRep ρ) :=
    endFieldRep_isAbsolutelyIrreducible ρ
  exact Theory.Representation.IsAbsolutelyIrreducible.irreducible_of_extension
    (ρ := endFieldRep ρ) k

theorem finrank_fixSubGen_extendScalars (k : Type*) [Field k]
    [Algebra (End F[G] ρ.asModule) k] (A : Subgroup G) :
    finrank k
        (fixSubGen (Theory.Representation.extendScalars k (endFieldRep ρ)) A) =
      finrank (End F[G] ρ.asModule) (fixSubGen (endFieldRep ρ) A) := by
  let K := End F[G] ρ.asModule
  have h := Walter.finrank_invariants_extendScalars (K := k)
    ((endFieldRep ρ).comp A.subtype : Representation K A ρ.asModule)
  rw [fixSubGen_eq_invariants, fixSubGen_eq_invariants]
  exact h

omit [Finite G] in
theorem finrank_tensorProduct_asModule (k : Type*) [Field k]
    [Algebra (End F[G] ρ.asModule) k] :
    finrank k (k ⊗[End F[G] ρ.asModule] ρ.asModule) =
      finrank (End F[G] ρ.asModule) ρ.asModule := by
  let : Module.Free (End F[G] ρ.asModule) ρ.asModule :=
    Module.Free.of_divisionRing _ _
  exact Module.finrank_baseChange (S := End F[G] ρ.asModule) (R := k)

end ExtendScalars

section Descent

variable [Finite G]

theorem conj_inv_mem_of_conj_mem {U : Subgroup G} {h : G}
    (hh : ∀ u ∈ U, h * u * h⁻¹ ∈ U) :
    ∀ u ∈ U, h⁻¹ * u * h ∈ U := by
  classical
  have hinj : Function.Injective fun x : U => (⟨h * x.1 * h⁻¹, hh x.1 x.2⟩ : U) := by
    intro x y hxy
    have hxy' : h * x.1 * h⁻¹ = h * y.1 * h⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (by
      have := mul_left_cancel (mul_right_cancel hxy')
      exact this)
  intro u hu
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj ⟨u, hu⟩
  have hw' : h * w.1 * h⁻¹ = u := congrArg Subtype.val hw
  have : w.1 = h⁻¹ * u * h := by
    rw [← hw']
    group
  rw [← this]
  exact w.2

theorem map_fixSubGen_of_conj_mem {U : Subgroup G} {h : G}
    (hh : ∀ u ∈ U, h * u * h⁻¹ ∈ U) (w : ρ.asModule)
    (hw : w ∈ fixSubGen (endFieldRep ρ) U) :
    endFieldRep ρ h w ∈ fixSubGen (endFieldRep ρ) U := by
  intro u hu
  have h' : u * h = h * (h⁻¹ * u * h) := by group
  calc endFieldRep ρ u (endFieldRep ρ h w)
      = endFieldRep ρ (u * h) w := by
        rw [← Module.End.mul_apply, ← map_mul]
    _ = endFieldRep ρ (h * (h⁻¹ * u * h)) w := by rw [h']
    _ = endFieldRep ρ h (endFieldRep ρ (h⁻¹ * u * h) w) := by
        rw [map_mul, Module.End.mul_apply]
    _ = endFieldRep ρ h w := by
        rw [hw _ (conj_inv_mem_of_conj_mem hh u hu)]

theorem exists_algebraMap_of_finrank_fixSubGen_eq_one (k : Type*) [Field k]
    [Algebra (End F[G] ρ.asModule) k] (U : Subgroup G) (h : G)
    (hh : ∀ u ∈ U, h * u * h⁻¹ ∈ U)
    (h1 : finrank k
      (fixSubGen (Theory.Representation.extendScalars k (endFieldRep ρ)) U) = 1) :
    ∃ c : End F[G] ρ.asModule,
      ∀ w ∈ fixSubGen (Theory.Representation.extendScalars k (endFieldRep ρ)) U,
        Theory.Representation.extendScalars k (endFieldRep ρ) h w =
          algebraMap (End F[G] ρ.asModule) k c • w := by
  classical
  let K := End F[G] ρ.asModule
  let M := ρ.asModule
  let σ := endFieldRep ρ
  let W := Theory.Representation.extendScalars k σ
  let C := fixSubGen σ U
  let CW := fixSubGen W U
  have : Finite V := Module.finite_iff_finite.mp ‹FiniteDimensional F V›
  have : Finite M := finite_asModule ρ
  have : Finite C := Subtype.finite
  have hdimC : finrank K C = 1 := by
    rw [← finrank_fixSubGen_extendScalars ρ k U]
    exact h1
  have hCinv : ∀ u ∈ U, h⁻¹ * u * h ∈ U := conj_inv_mem_of_conj_mem hh
  let ψ : C →ₗ[K] C :=
    { toFun := fun w => ⟨σ h w.1, map_fixSubGen_of_conj_mem ρ hh w.1 w.2⟩
      map_add' := fun x y => by
        ext
        exact map_add (σ h) x.1 y.1
      map_smul' := fun a x => by
        ext
        exact LinearMap.map_smul (σ h) a x.1 }
  have : Module.Free K C := Module.Free.of_divisionRing K C
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdimC ψ
  have hmem : ∀ w ∈ C, σ h w = c • w := by
    intro w hw
    have := congrArg (fun f : C →ₗ[K] C => f ⟨w, hw⟩) hc
    simpa [ψ] using this
  obtain ⟨v, hv0, -⟩ := finrank_eq_one_iff'.mp hdimC
  have hvne : v.1 ≠ 0 := fun hv => hv0 (Subtype.ext hv)
  have hmemW : ((1 : k) ⊗ₜ[K] v.1) ∈ CW := by
    intro u hu
    show W u ((1 : k) ⊗ₜ[K] v.1) = (1 : k) ⊗ₜ[K] v.1
    rw [show W u = (σ u).baseChange k from rfl, LinearMap.baseChange_tmul,
      v.2 u hu]
  have h1t : (1 : k) ⊗ₜ[K] v.1 ≠ 0 := by
    intro hz
    exact hvne ((Module.FaithfullyFlat.one_tmul_eq_zero_iff K M (A := k) v.1).mp hz)
  have hCW : CW = k ∙ ((1 : k) ⊗ₜ[K] v.1) := by
    refine (Submodule.eq_of_le_of_finrank_eq
      (S₁ := k ∙ ((1 : k) ⊗ₜ[K] v.1)) (S₂ := CW) ?_ ?_).symm
    · rw [Submodule.span_le]
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hmemW
    · rw [finrank_span_singleton h1t, h1]
  have hscalar (d : K) (m : M) :
      (1 : k) ⊗ₜ[K] (d • m) = algebraMap K k d • ((1 : k) ⊗ₜ[K] m) := by
    rw [TensorProduct.tmul_smul]
    simp
  have hx : W h ((1 : k) ⊗ₜ[K] v.1) =
      algebraMap K k c • ((1 : k) ⊗ₜ[K] v.1) := by
    rw [show W h = (σ h).baseChange k from rfl, LinearMap.baseChange_tmul, hmem v v.2]
    exact hscalar c v.1
  refine ⟨c, fun w hw => ?_⟩
  have hw' : w ∈ k ∙ ((1 : k) ⊗ₜ[K] v.1) := by rwa [← hCW]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw'
  rw [← ha, map_smul, hx, smul_comm]

end Descent

end CFSG.HardMathSupport.GuralnickMalle
