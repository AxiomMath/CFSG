module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthEigen

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {i : V ≃ₗ[F] V}

section Ext

@[expose] noncomputable def projMW (i : V ≃ₗ[F] V) (hii : i * i = 1) : V →ₗ[F] minusSp i :=
  LinearMap.codRestrict (minusSp i) (projM i) (projM_mem hii)

theorem projMW_apply (hii : i * i = 1) (x : V) : (projMW i hii x : V) = projM i x := rfl

@[expose] noncomputable def extLin (hii : i * i = 1) (g : minusSp i ≃ₗ[F] minusSp i) :
    V →ₗ[F] V :=
  (minusSp i).subtype ∘ₗ (g : minusSp i →ₗ[F] minusSp i) ∘ₗ projMW i hii + projP i

theorem extLin_apply (hii : i * i = 1) (g : minusSp i ≃ₗ[F] minusSp i) (x : V) :
    extLin hii g x = ((g ⟨projM i x, projM_mem hii x⟩ : minusSp i) : V) + projP i x := rfl

theorem extLin_apply_add (h2 : (2 : F) ≠ 0) (hii : i * i = 1) (g : minusSp i ≃ₗ[F] minusSp i)
    {u v : V} (hu : u ∈ plusSp i) (hv : v ∈ minusSp i) :
    extLin hii g (u + v) = ((g ⟨v, hv⟩ : minusSp i) : V) + u := by
  rw [extLin_apply]
  have h1 := projM_add_of_mem h2 hu hv
  have h3 := projP_add_of_mem h2 hu hv
  have : (⟨projM i (u + v), projM_mem hii (u + v)⟩ : minusSp i) = ⟨v, hv⟩ := Subtype.ext h1
  rw [this, h3]

theorem extLin_mul (h2 : (2 : F) ≠ 0) (hii : i * i = 1) (g g' : minusSp i ≃ₗ[F] minusSp i)
    (x : V) : extLin hii (g * g') x = extLin hii g (extLin hii g' x) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
  rw [extLin_apply_add h2 hii g' hu hv, add_comm ((g' ⟨v, hv⟩ : minusSp i) : V) u,
    extLin_apply_add h2 hii g hu (g' ⟨v, hv⟩).2, extLin_apply_add h2 hii (g * g') hu hv]
  rfl

theorem extLin_one (h2 : (2 : F) ≠ 0) (hii : i * i = 1) (x : V) : extLin hii 1 x = x := by
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
  rw [extLin_apply_add h2 hii 1 hu hv]
  change v + u = u + v
  exact add_comm _ _

@[expose] noncomputable def extGrp (h2 : (2 : F) ≠ 0) (hii : i * i = 1) :
    (minusSp i ≃ₗ[F] minusSp i) →* (V ≃ₗ[F] V) where
  toFun g := LinearEquiv.ofLinearMap (extLin hii g) (extLin hii g⁻¹)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← extLin_mul h2 hii g g⁻¹, mul_inv_cancel, extLin_one h2 hii]
      rfl)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← extLin_mul h2 hii g⁻¹ g, inv_mul_cancel, extLin_one h2 hii]
      rfl)
  map_one' := LinearEquiv.ext fun x => extLin_one h2 hii x
  map_mul' g g' := LinearEquiv.ext fun x => extLin_mul h2 hii g g' x

theorem extGrp_apply (h2 : (2 : F) ≠ 0) (hii : i * i = 1) (g : minusSp i ≃ₗ[F] minusSp i)
    (x : V) : extGrp h2 hii g x = extLin hii g x := rfl

theorem extGrp_apply_add (h2 : (2 : F) ≠ 0) (hii : i * i = 1) (g : minusSp i ≃ₗ[F] minusSp i)
    {u v : V} (hu : u ∈ plusSp i) (hv : v ∈ minusSp i) :
    extGrp h2 hii g (u + v) = ((g ⟨v, hv⟩ : minusSp i) : V) + u :=
  extLin_apply_add h2 hii g hu hv

theorem extGrp_injective (h2 : (2 : F) ≠ 0) (hii : i * i = 1) :
    Function.Injective (extGrp h2 hii) := by
  intro g g' h
  refine LinearEquiv.ext fun v => ?_
  have := LinearEquiv.congr_fun h (0 + v.1)
  rw [extGrp_apply_add h2 hii g (Submodule.zero_mem _) v.2,
    extGrp_apply_add h2 hii g' (Submodule.zero_mem _) v.2] at this
  exact Subtype.ext (by simpa using this)

@[expose] noncomputable def restrictMinus (h : V ≃ₗ[F] V) (hc : h * i = i * h) :
    minusSp i ≃ₗ[F] minusSp i where
  toFun x := ⟨h x, map_mem_minusSp hc x.2⟩
  map_add' x y := Subtype.ext (map_add h (x : V) (y : V))
  map_smul' c x := Subtype.ext (map_smul h c (x : V))
  invFun x := ⟨h⁻¹ x, map_mem_minusSp (inv_mul_eq_mul_inv_of hc) x.2⟩
  left_inv x := Subtype.ext (LinearEquiv.inv_apply_apply' h x)
  right_inv x := Subtype.ext (LinearEquiv.apply_inv_apply' h x)

theorem restrictMinus_apply (h : V ≃ₗ[F] V) (hc : h * i = i * h) (x : minusSp i) :
    ((restrictMinus h hc x : minusSp i) : V) = h x := rfl

theorem extGrp_mem_nM (h2 : (2 : F) ≠ 0) (hii : i * i = 1)
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {g : minusSp i ≃ₗ[F] minusSp i}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (minusSp i))) :
    extGrp h2 hii g ∈ nM Q i := by
  have hgQ : ∀ x : minusSp i, Q (g x : V) = Q (x : V) := fun x =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg x
  refine ⟨?_, ?_, fun u hu => ?_⟩
  · refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
    rw [extGrp_apply_add h2 hii g hu hv, QuadraticMap.map_add Q, QuadraticMap.map_add Q u v,
      hgQ ⟨v, hv⟩, polar_comm, polar_plusSp_minusSp h2 hi hu (g ⟨v, hv⟩).2,
      polar_plusSp_minusSp h2 hi hu hv]
    ring
  · refine LinearEquiv.ext fun x => ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
    have e1 : i (u + v) = u + -v := by
      rw [map_add, mem_plusSp.mp hu, mem_minusSp.mp hv]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1,
      extGrp_apply_add h2 hii g hu (Submodule.neg_mem _ hv), extGrp_apply_add h2 hii g hu hv,
      map_add, mem_plusSp.mp hu, mem_minusSp.mp (g ⟨v, hv⟩).2]
    have : (g ⟨-v, Submodule.neg_mem _ hv⟩ : minusSp i) = -(g ⟨v, hv⟩) := by
      rw [← map_neg]; rfl
    rw [this, Submodule.coe_neg]
  · have := extGrp_apply_add h2 hii g hu (Submodule.zero_mem _)
    rw [add_zero] at this
    rw [this]
    have h0 : (⟨0, Submodule.zero_mem _⟩ : minusSp i) = 0 := rfl
    rw [h0, map_zero]
    simp

theorem nM_le_map_extGrp (h2 : (2 : F) ≠ 0) (hii : i * i = 1) {h : V ≃ₗ[F] V}
    (hh : h ∈ nM Q i) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (minusSp i)), extGrp h2 hii g = h := by
  obtain ⟨hO, hc, hf⟩ := hh
  refine ⟨restrictMinus h hc, ?_, ?_⟩
  · refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    exact map_of_mem hO (x : V)
  · refine LinearEquiv.ext fun x => ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
    rw [extGrp_apply_add h2 hii _ hu hv, restrictMinus_apply, map_add, hf u hu, add_comm]

theorem nM_eq_map_extGrp (h2 : (2 : F) ≠ 0) (hii : i * i = 1)
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    nM Q i = (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (minusSp i))).map
      (extGrp h2 hii) := by
  ext h
  constructor
  · intro hh
    obtain ⟨g, hg, rfl⟩ := nM_le_map_extGrp h2 hii hh
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact extGrp_mem_nM h2 hii hi hg

end Ext

end CFSG.ClassicalInvolution.ModelFacts
