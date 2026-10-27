module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension

open Module DirectSum

variable {F V I : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [Fintype I] [DecidableEq I]

@[expose] def commutant (T : Module.End F V) : Submodule F (Module.End F V) where
  carrier := {S | S.comp T = T.comp S}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.add_comp, LinearMap.comp_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.smul_comp, LinearMap.comp_smul, ha]

theorem mem_commutant {T S : Module.End F V} : S ∈ commutant T ↔ S.comp T = T.comp S := Iff.rfl

@[expose] noncomputable def decompEquiv (U : I → Submodule F V) (hU : DirectSum.IsInternal U) :
    (⨁ i, U i) ≃ₗ[F] V :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap U) hU

theorem decompEquiv_apply (U : I → Submodule F V) (hU : DirectSum.IsInternal U)
    (y : ⨁ i
, U i) : decompEquiv U hU y = ∑ j, ((y j : U j) : V) := by
  have h : ∀ z, decompEquiv U hU z = DirectSum.coeLinearMap U z := fun _ => rfl
  conv_lhs => rw [← DirectSum.sum_univ_of y]
  simp only [h, map_sum, DirectSum.coeLinearMap_of]

theorem decompEquiv_symm_of (U : I → Submodule F V) (hU : DirectSum.IsInternal U) (i : I)
    (u : U i) : (decompEquiv U hU).symm (u : V) = DirectSum.of (fun j => U j) i u := by
  rw [LinearEquiv.symm_apply_eq, decompEquiv_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp only [Submodule.coe_zero] at *
    rw [DirectSum.of_eq_of_ne _ _ _ hj]; rfl
  · simp

theorem maps_to {lam : I → F} (hlam : Function.Injective lam) {U : I → Submodule F V}
    (hU : DirectSum.IsInternal U) {T : Module.End F V}
    (hT : ∀ i, ∀ u ∈ U i, T u = lam i • u) {S : Module.End F V} (hS : S ∈ commutant T)
    (i : I) (u : V) (hu : u ∈ U i) : S u ∈ U i := by
  set e := decompEquiv U hU with he
  obtain ⟨x, hx⟩ := e.surjective (S u)
  have h1 : T (S u) = lam i • S u := by
    have := LinearMap.congr_fun hS u
    simp only [LinearMap.comp_apply] at this
    rw [← this, hT i u hu, map_smul]
  have h2 : T (S u) = ∑ j, lam j • ((x j : U j) : V) := by
    rw [← hx, he, decompEquiv_apply, map_sum]
    exact Finset.sum_congr rfl (fun j _ => hT j _ (x j).2)
  have h3 : ∑ j, (lam j - lam i) • ((x j : U j) : V) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
    rw [← h2, h1, ← hx, he, decompEquiv_apply, sub_self]
  have h4 : e (∑ j, DirectSum.of (fun j => U j) j ((lam j - lam i) • x j)) = 0 := by
    rw [map_sum, ← h3]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [he, decompEquiv_apply, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      rw [DirectSum.of_eq_of_ne _ _ _ hk]; rfl
    · simp
  have h5 := e.injective (h4.trans (map_zero e).symm)
  have h6 : ∀ j, j ≠ i → x j = 0 := by
    intro j hj
    have := congrArg (fun z => z j) h5
    simp only [DirectSum.sum_univ_of] at this
    rw [DFinsupp.finset_sum_apply, Finset.sum_eq_single j] at this
    · simp only [DirectSum.of_eq_same, DirectSum.zero_apply, smul_eq_zero, sub_eq_zero] at this
      rcases this with h | h
      · exact absurd (hlam h) hj
      · exact h
    · intro k _ hk
      rw [DirectSum.of_eq_of_ne _ _ _ hk.symm]
    · simp
  rw [← hx, he, decompEquiv_apply, Finset.sum_eq_single i]
  · exact (x i).2
  · intro j _ hj
    simp [h6 j hj]
  · simp

theorem decompEquiv_of (U : I → Submodule F V) (hU : DirectSum.IsInternal U) (i : I)
    (u : U i) : decompEquiv U hU (DirectSum.of (fun j => U j) i u) = (u : V) := by
  rw [← decompEquiv_symm_of U hU i u]; simp

theorem ext_U (U : I → Submodule F V) (hU : DirectSum.IsInternal U) {g h : Module.End F V}
    (H : ∀ i, ∀ u ∈ U i, g u = h u) : g = h := by
  ext v
  obtain ⟨y, rfl⟩ := (decompEquiv U hU).surjective v
  rw [← DirectSum.sum_univ_of y, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [decompEquiv_of]
  exact H j _ (y j).2

@[expose] noncomputable def assemble (U : I → Submodule F V) (hU : DirectSum.IsInternal U) :
    (∀ i, Module.End F (U i)) →ₗ[F] Module.End F V where
  toFun f := (decompEquiv U hU).toLinearMap ∘ₗ DirectSum.lmap (fun i => (f i)) ∘ₗ
    (decompEquiv U hU).symm.toLinearMap
  map_add' f g := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearEquiv.coe_coe, ← map_add]
    congr 1
    ext j
    simp
  map_smul' c f := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
      RingHom.id_apply]
    rw [← map_smul (decompEquiv U hU)]
    refine congrArg _ ?_
    refine DFinsupp.ext (fun j => ?_)
    simp only [DirectSum.lmap_apply, Pi.smul_apply, LinearMap.smul_apply]
    rfl

theorem assemble_apply (U : I → Submodule F V) (hU : DirectSum.IsInternal U)
    (f : ∀ i, Module.End F (U i)) (i : I) (u : U i) :
    assemble U hU f (u : V) = (f i u : V) := by
  simp only [assemble, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    decompEquiv_symm_of]
  have : DirectSum.lmap (fun i => f i) (DirectSum.of (fun j => U j) i u)
      = DirectSum.of (fun j => U j) i (f i u) := by
    simpa [DirectSum.lof_eq_of] using DirectSum.lmap_lof (fun i => f i) i u
  rw [this, decompEquiv_of]

theorem assemble_mem_commutant {lam : I → F} {U : I → Submodule F V}
    (hU : DirectSum.IsInternal U) {T : Module.End F V}
    (hT : ∀ i, ∀ u ∈ U i, T u = lam i • u) (f : ∀ i, Module.End F (U i)) :
    assemble U hU f ∈ commutant T := by
  rw [mem_commutant]
  refine ext_U U hU (fun i u hu => ?_)
  have h1 : T u = lam i • u := hT i u hu
  have h2 : assemble U hU f u = ((f i ⟨u, hu⟩ : U i) : V) := assemble_apply U hU f i ⟨u, hu⟩
  have h3 : assemble U hU f (T u) = lam i • ((f i ⟨u, hu⟩ : U i) : V) := by
    rw [h1, map_smul, h2]
  simp only [LinearMap.comp_apply]
  rw [h3, h2]
  exact (hT i _ ((f i ⟨u, hu⟩).2)).symm

@[expose] noncomputable def commutantEquiv {lam : I → F} (hlam : Function.Injective lam)
    {U : I → Submodule F V} (hU : DirectSum.IsInternal U) {T : Module.End F V}
    (hT : ∀ i, ∀ u ∈ U i, T u = lam i • u) :
    (∀ i, Module.End F (U i)) ≃ₗ[F] commutant T :=
  LinearEquiv.ofBijective
    ((assemble U hU).codRestrict (commutant T) (assemble_mem_commutant hU hT))
    ⟨by
      intro f g hfg
      have h : assemble U hU f = assemble U hU g := congrArg Subtype.val hfg
      funext i
      ext u
      have := LinearMap.congr_fun h (u : V)
      rw [assemble_apply, assemble_apply] at this
      exact this,
     by
      intro S
      refine ⟨fun i => LinearMap.restrict S.1 (fun u hu => maps_to hlam hU hT S.2 i u hu), ?_⟩
      apply Subtype.ext
      refine ext_U U hU (fun i u hu => ?_)
      have := assemble_apply U hU
        (fun i => LinearMap.restrict S.1 (fun u hu => maps_to hlam hU hT S.2 i u hu)) i ⟨u, hu⟩
      simpa using this⟩

theorem finrank_eq {lam : I → F} (hlam : Function.Injective lam)
    {U : I → Submodule F V} (hU : DirectSum.IsInternal U) {T : Module.End F V}
    (hT : ∀ i, ∀ u ∈ U i, T u = lam i • u) :
    finrank F (commutant T) = ∑ i, (finrank F (U i)) ^ 2 := by
  rw [← (commutantEquiv hlam hU hT).finrank_eq, Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Module.finrank_linearMap, sq]

theorem sum_finrank_eq {U : I → Submodule F V} (hU : DirectSum.IsInternal U) :
    ∑ i, finrank F (U i) = finrank F V := by
  rw [← (decompEquiv U hU).finrank_eq, Module.finrank_directSum]

end CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension
