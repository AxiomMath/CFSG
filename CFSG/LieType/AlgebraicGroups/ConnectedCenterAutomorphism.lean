module

public import CFSG.LieType.AlgebraicGroups.CanonicalReductiveFactors
public import CFSG.LieType.AlgebraicGroups.CentralIsogenyLift
public import CFSG.LieType.AlgebraicGroups.CentralProductMorphism
public import TauCeti.Algebra.AlgebraicGroup.Center.Isomorphism

public noncomputable section

open CategoryTheory AlgebraicGeometry WithConv
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.CanonicalReductive

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)

theorem reducedCenterTensorReduced :
    let C : Type u := TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra M.obj
    IsReduced ((C ⧸ nilradical C) ⊗[k] (C ⧸ nilradical C)) := by
  let C : Type u := TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra M.obj
  have : Algebra.FiniteType k C := inferInstance
  have : IsReduced (C ⧸ nilradical C) := TauCeti.isReduced_quotient_nilradical C
  have : Algebra.FiniteType k (C ⧸ nilradical C) :=
    Algebra.FiniteType.quotient k (nilradical C)
  exact TauCeti.instIsReducedTensorProductOfIsAlgClosed k (C ⧸ nilradical C) (C ⧸ nilradical C)

section Core

variable (σ : M →ₐc[k] M)
omit [IsAlgClosed k] in
theorem aut_bijective (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) :
    Function.Bijective σ := by
  constructor
  · intro x y hxy
    have hx : σ (σ (σ x)) = x := by
      simpa only [BialgHom.comp_apply, BialgHom.id_apply] using
        congrArg (fun f : M →ₐc[k] M => f x) hσ3
    have hy : σ (σ (σ y)) = y := by
      simpa only [BialgHom.comp_apply, BialgHom.id_apply] using
        congrArg (fun f : M →ₐc[k] M => f y) hσ3
    calc
      x = σ (σ (σ x)) := hx.symm
      _ = σ (σ (σ y)) := congrArg (fun z => σ (σ z)) hxy
      _ = y := hy
  · intro y
    refine ⟨σ (σ y), ?_⟩
    simpa only [BialgHom.comp_apply, BialgHom.id_apply] using
      congrArg (fun f : M →ₐc[k] M => f y) hσ3

noncomputable def autIso (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) :
    M.obj ≅ M.obj :=
  _root_.CommHopfAlgCat.isoMk (BialgEquiv.ofBijective σ (aut_bijective M σ hσ3))

omit [IsAlgClosed k] in
@[simp]
theorem autIso_hom_hom (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) :
    (autIso M σ hσ3).hom.hom = σ := by
  rw [autIso, _root_.CommHopfAlgCat.isoMk_hom, _root_.CommHopfAlgCat.hom_ofHom]
  rfl

theorem identityComponentHopfIdeal_comapOfSurjective_eq_self
    (H : _root_.CommHopfAlgCat.{u} k) [Algebra.FiniteType k H] (e : H ≅ H) :
    (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).comapOfSurjective
        e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2 =
      TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) := by
  let I := TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let _ : LocallyConnectedSpace (PrimeSpectrum H) := inferInstance
  let q : H ⟶ TauCeti.CommHopfAlgCat.quotient H I :=
    TauCeti.CommHopfAlgCat.mkQuotient H I
  let _ : ConnectedSpace (PrimeSpectrum (TauCeti.CommHopfAlgCat.quotient H I)) := by
    change ConnectedSpace (PrimeSpectrum (H ⧸ I.toIdeal))
    rw [show I.toIdeal = PrimeSpectrum.connectedComponentIdeal
        (TauCeti.Bialgebra.augmentationPoint k H) from by
      simpa only [I] using
        (TauCeti.HopfAlgebra.identityComponentHopfIdeal_toIdeal (k := k) (H := H))]
    exact PrimeSpectrum.connectedSpace_quotient_connectedComponentIdeal
      (TauCeti.Bialgebra.augmentationPoint k H)
  have hmap : I.map e.hom.hom ≤ I := by
    rw [TauCeti.HopfIdeal.map_le_iff]
    intro x hx
    have hle : I.toIdeal ≤ RingHom.ker (e.hom ≫ q).hom.toAlgHom.toRingHom :=
      TauCeti.CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected
        (e.hom ≫ q)
    have hkill : (e.hom ≫ q).hom x = 0 :=
      hle (TauCeti.HopfIdeal.mem_toIdeal.mpr hx)
    rw [_root_.CommHopfAlgCat.comp_apply] at hkill
    exact (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff H I (e.hom.hom x)).mp hkill
  have hmap_inv : I.map e.inv.hom ≤ I := by
    rw [TauCeti.HopfIdeal.map_le_iff]
    intro x hx
    have hle : I.toIdeal ≤ RingHom.ker (e.inv ≫ q).hom.toAlgHom.toRingHom :=
      TauCeti.CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected
        (e.inv ≫ q)
    have hkill : (e.inv ≫ q).hom x = 0 :=
      hle (TauCeti.HopfIdeal.mem_toIdeal.mpr hx)
    rw [_root_.CommHopfAlgCat.comp_apply] at hkill
    exact (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff H I (e.inv.hom x)).mp hkill
  have hmap_eq : I.map e.hom.hom = I := by
    apply le_antisymm hmap
    intro x hx
    have hxinv : e.inv.hom x ∈ I :=
      hmap_inv (TauCeti.HopfIdeal.mem_map_of_mem (e.inv.hom) hx)
    have hcancel : e.hom.hom (e.inv.hom x) = x := by
      have h := congrArg (fun f : H ⟶ H => f.hom x) e.inv_hom_id
      simpa only [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.id_apply] using h
    rw [← hcancel]
    exact TauCeti.HopfIdeal.mem_map_of_mem (e.hom.hom) hxinv
  have hmap_ideal : Ideal.map (e.hom.hom : H →+* H) I.toIdeal = I.toIdeal := by
    simpa only [TauCeti.HopfIdeal.map_toIdeal] using
      congrArg TauCeti.HopfIdeal.toIdeal hmap_eq
  let eB : H ≃ₐc[k] H := _root_.CommHopfAlgCat.ofIso e
  let eRing : H ≃+* H := eB.toAlgEquiv.toRingEquiv
  have hfun : (eRing : H → H) = (e.hom.hom : H → H) := by
    ext y
    simp only [eRing, eB, AlgEquiv.coe_ringEquiv', BialgEquiv.coe_toAlgEquiv,
      _root_.CommHopfAlgCat.ofIso_apply]
  have hmap_ideal' : Ideal.map (eRing : H →+* H) I.toIdeal = I.toIdeal := by
    rw [show (eRing : H →+* H) = (e.hom.hom : H →+* H) from by
      ext y
      exact congrFun hfun y]
    exact hmap_ideal
  have hsymm : Ideal.comap (eRing.symm : H →+* H) I.toIdeal = I.toIdeal := by
    have h := Ideal.map_comap_of_equiv (f := eRing) (I := I.toIdeal)
    rw [hmap_ideal'] at h
    exact h.symm
  have hcomap : Ideal.comap (eRing : H →+* H) I.toIdeal = I.toIdeal := by
    have h := Ideal.comap_of_equiv (f := eRing) (I := I.toIdeal)
    rw [hsymm] at h
    exact h
  apply TauCeti.HopfIdeal.ext
  intro x
  rw [TauCeti.HopfIdeal.mem_comapOfSurjective]
  rw [show e.hom.hom x = eRing x from (congrFun hfun x).symm]
  change (eRing : H →+* H) x ∈ I.toIdeal ↔ x ∈ I.toIdeal
  have hiff : x ∈ I.toIdeal ↔ (eRing : H →+* H) x ∈ I.toIdeal := by
    have h1 : x ∈ I.toIdeal ↔ x ∈ Ideal.comap (eRing : H →+* H) I.toIdeal := by
      rw [hcomap]
    rw [h1]
    exact Ideal.mem_comap
  exact hiff.symm

omit [IsAlgClosed k] in
theorem comap_nilradical_eq_self_of_bialg_iso
    (H : _root_.CommHopfAlgCat.{u} k) (e : H ≅ H) :
    Ideal.comap (e.hom.hom : H →+* H) (nilradical H) = nilradical H := by
  let eB : H ≃ₐc[k] H := _root_.CommHopfAlgCat.ofIso e
  let eRing : H ≃+* H := eB.toAlgEquiv.toRingEquiv
  have hfun : (eRing : H → H) = (e.hom.hom : H → H) := by
    ext y
    simp only [eRing, eB, AlgEquiv.coe_ringEquiv', BialgEquiv.coe_toAlgEquiv,
      _root_.CommHopfAlgCat.ofIso_apply]
  have hmap : Ideal.map (eRing : H →+* H) (nilradical H) = nilradical H := by
    have hker : RingHom.ker (eRing : H →+* H) ≤ (⊥ : Ideal H) :=
      (RingHom.ker_equiv eRing).le
    have h := Ideal.map_radical_of_surjective (f := (eRing : H →+* H)) eRing.surjective hker
    rw [Ideal.map_bot] at h
    simpa only [nilradical, Ideal.zero_eq_bot] using h
  have hsymm : Ideal.comap (eRing.symm : H →+* H) (nilradical H) = nilradical H := by
    have h := Ideal.map_comap_of_equiv (f := eRing) (I := nilradical H)
    rw [hmap] at h
    exact h.symm
  have hcomap : Ideal.comap (eRing : H →+* H) (nilradical H) = nilradical H := by
    have h := Ideal.comap_of_equiv (f := eRing) (I := nilradical H)
    rw [hsymm] at h
    exact h
  rw [show (e.hom.hom : H →+* H) = (eRing : H →+* H) from by
    ext y
    exact (congrFun hfun y).symm]
  exact hcomap

noncomputable abbrev centerObj (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k) :
    _root_.CommHopfAlgCat.{u} k :=
  TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra M.obj

noncomputable abbrev centerReductionIdeal (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k) :
    TauCeti.HopfIdeal k (centerObj M) :=
  letI := reducedCenterTensorReduced M
  TauCeti.HopfIdeal.reduction k (centerObj M)

noncomputable abbrev reducedCenterObj (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k) :
    _root_.CommHopfAlgCat.{u} k :=
  letI := reducedCenterTensorReduced M
  TauCeti.CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra M.obj

noncomputable def reducedCenterIso (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (σ : M →ₐc[k] M) (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) :
    reducedCenterObj M ≅ reducedCenterObj M := by
  letI := reducedCenterTensorReduced M
  let C := TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra M.obj
  let J := TauCeti.HopfIdeal.reduction k C
  let e : C ≅ C :=
    TauCeti.CommHopfAlgCat.centerCoordinateIso (autIso M σ hσ3)
  have hJ : J.comapOfSurjective e.hom.hom
      (ConcreteCategory.bijective_of_isIso e.hom).2 = J := by
    apply TauCeti.HopfIdeal.ext
    intro x
    rw [TauCeti.HopfIdeal.mem_comapOfSurjective]
    rw [← TauCeti.HopfIdeal.mem_toIdeal, TauCeti.HopfIdeal.reduction_toIdeal,
      ← TauCeti.HopfIdeal.mem_toIdeal, TauCeti.HopfIdeal.reduction_toIdeal]
    have hcomap := comap_nilradical_eq_self_of_bialg_iso (H := C) e
    have hiff : x ∈ nilradical C ↔ e.hom.hom x ∈ nilradical C := by
      have h1 : x ∈ nilradical C ↔
          x ∈ Ideal.comap (e.hom.hom : C →+* C) (nilradical C) := by
        rw [hcomap]
      rw [h1]
      exact Ideal.mem_comap
    exact hiff.symm
  exact TauCeti.CommHopfAlgCat.quotientIsoOfComapEq e J hJ

noncomputable def sigmaReducedCenter (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (σ : M →ₐc[k] M) (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) :
    reducedCenterObj M →ₐc[k] reducedCenterObj M :=
  (reducedCenterIso M σ hσ3).hom.hom

omit [IsAlgClosed k] in
theorem centerCoordinateMap_mkQuotient (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (e : M.obj ≅ M.obj) (x : M.obj) :
    (TauCeti.CommHopfAlgCat.centerCoordinateMap e).hom
        (TauCeti.CommHopfAlgCat.mkQuotient M.obj
          (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj) x) =
      TauCeti.CommHopfAlgCat.mkQuotient M.obj
        (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj) (e.hom.hom x) := by
  rw [TauCeti.CommHopfAlgCat.mkQuotient_apply,
    TauCeti.CommHopfAlgCat.mkQuotient_apply, Ideal.Quotient.mkₐ_eq_mk]
  exact TauCeti.CommHopfAlgCat.centerCoordinateMap_mk e x

omit [IsAlgClosed k] in
theorem centerIso_apply_mk (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (σ : M →ₐc[k] M) (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) (x : M.obj) :
    (TauCeti.CommHopfAlgCat.centerCoordinateIso (autIso M σ hσ3)).hom.hom
        (TauCeti.CommHopfAlgCat.mkQuotient M.obj
          (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj) x) =
      TauCeti.CommHopfAlgCat.mkQuotient M.obj
        (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj)
        ((autIso M σ hσ3).hom.hom x) := by
  rw [TauCeti.CommHopfAlgCat.centerCoordinateIso_hom]
  exact centerCoordinateMap_mkQuotient M (autIso M σ hσ3) x

omit [IsAlgClosed k] in
theorem autIso_cube_apply (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (σ : M →ₐc[k] M) (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) (x : M.obj) :
    (autIso M σ hσ3).hom.hom
        ((autIso M σ hσ3).hom.hom ((autIso M σ hσ3).hom.hom x)) = x := by
  rw [autIso_hom_hom M σ hσ3]
  simpa only [BialgHom.comp_apply, BialgHom.id_apply] using
    congrArg (fun f : M →ₐc[k] M => f x) hσ3

omit [IsAlgClosed k] in
theorem centerIso_cube_apply (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (σ : M →ₐc[k] M) (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M)
    (x : TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra M.obj) :
    (TauCeti.CommHopfAlgCat.centerCoordinateIso (autIso M σ hσ3)).hom.hom
        ((TauCeti.CommHopfAlgCat.centerCoordinateIso (autIso M σ hσ3)).hom.hom
          ((TauCeti.CommHopfAlgCat.centerCoordinateIso (autIso M σ hσ3)).hom.hom x)) = x := by
  obtain ⟨y, rfl⟩ := TauCeti.CommHopfAlgCat.mkQuotient_surjective M.obj
    (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj) x
  rw [centerIso_apply_mk M σ hσ3,
    centerIso_apply_mk M σ hσ3,
    centerIso_apply_mk M σ hσ3,
    autIso_cube_apply M σ hσ3]

theorem mkQuotient_comp_reducedCenterIso_hom
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (σ : M →ₐc[k] M) (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) :
    TauCeti.CommHopfAlgCat.mkQuotient (centerObj M) (centerReductionIdeal M) ≫
        (reducedCenterIso M σ hσ3).hom =
      (TauCeti.CommHopfAlgCat.centerCoordinateIso (autIso M σ hσ3)).hom ≫
        TauCeti.CommHopfAlgCat.mkQuotient (centerObj M) (centerReductionIdeal M) := by
  unfold reducedCenterIso
  dsimp only
  rw [TauCeti.CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom]

theorem sigmaReducedCenter_apply_mk
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (σ : M →ₐc[k] M) (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) (x : centerObj M) :
    sigmaReducedCenter M σ hσ3
        (TauCeti.CommHopfAlgCat.mkQuotient (centerObj M) (centerReductionIdeal M) x) =
      TauCeti.CommHopfAlgCat.mkQuotient (centerObj M) (centerReductionIdeal M)
        ((TauCeti.CommHopfAlgCat.centerCoordinateIso (autIso M σ hσ3)).hom.hom x) := by
  have h := congrArg
    (fun f : centerObj M ⟶ reducedCenterObj M => f.hom x)
    (mkQuotient_comp_reducedCenterIso_hom M σ hσ3)
  rw [sigmaReducedCenter]
  change (reducedCenterIso M σ hσ3).hom.hom
      ((TauCeti.CommHopfAlgCat.mkQuotient (centerObj M) (centerReductionIdeal M)).hom x) =
    (TauCeti.CommHopfAlgCat.mkQuotient (centerObj M) (centerReductionIdeal M)).hom
      ((TauCeti.CommHopfAlgCat.centerCoordinateIso (autIso M σ hσ3)).hom.hom x)
  exact h

theorem sigmaReducedCenter_cube
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (σ : M →ₐc[k] M) (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) :
    (sigmaReducedCenter M σ hσ3 |>.comp (sigmaReducedCenter M σ hσ3)).comp
        (sigmaReducedCenter M σ hσ3) = BialgHom.id k (reducedCenterObj M) := by
  apply BialgHom.ext
  intro y
  obtain ⟨x, rfl⟩ := TauCeti.CommHopfAlgCat.mkQuotient_surjective (centerObj M)
    (centerReductionIdeal M) y
  rw [BialgHom.comp_apply, BialgHom.comp_apply, BialgHom.id_apply]
  rw [sigmaReducedCenter_apply_mk M σ hσ3,
    sigmaReducedCenter_apply_mk M σ hσ3,
    sigmaReducedCenter_apply_mk M σ hσ3,
    centerIso_cube_apply M σ hσ3]

noncomputable def sigmaConnectedCenter (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (σ : M →ₐc[k] M) (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) :
    (connectedCenter M : Type u) →ₐc[k] (connectedCenter M : Type u) := by
  letI : Algebra.FiniteType k (reducedCenterObj M) := inferInstance
  let I := TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := reducedCenterObj M)
  let e := reducedCenterIso M σ hσ3
  have hI : I.comapOfSurjective e.hom.hom
      (ConcreteCategory.bijective_of_isIso e.hom).2 = I :=
    identityComponentHopfIdeal_comapOfSurjective_eq_self (H := reducedCenterObj M) e
  exact (TauCeti.CommHopfAlgCat.quotientIsoOfComapEq e I hI).hom.hom

theorem sigmaConnectedCenter_apply_mk
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (σ : M →ₐc[k] M) (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M)
    (x : reducedCenterObj M) :
    let : Algebra.FiniteType k (reducedCenterObj M) := inferInstance
    let I := TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := reducedCenterObj M)
    sigmaConnectedCenter M σ hσ3
        (TauCeti.CommHopfAlgCat.mkQuotient (reducedCenterObj M) I x) =
      TauCeti.CommHopfAlgCat.mkQuotient (reducedCenterObj M) I
        (sigmaReducedCenter M σ hσ3 x) := by
  let : Algebra.FiniteType k (reducedCenterObj M) := inferInstance
  let I := TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := reducedCenterObj M)
  let e := reducedCenterIso M σ hσ3
  let hI := identityComponentHopfIdeal_comapOfSurjective_eq_self
    (H := reducedCenterObj M) e
  unfold sigmaConnectedCenter
  dsimp only
  change (TauCeti.CommHopfAlgCat.quotientIsoOfComapEq e I hI).hom.hom
      (TauCeti.CommHopfAlgCat.mkQuotient (reducedCenterObj M) I x) =
    TauCeti.CommHopfAlgCat.mkQuotient (reducedCenterObj M) I (e.hom.hom x)
  have h := congrArg
    (fun f : reducedCenterObj M ⟶ TauCeti.CommHopfAlgCat.quotient (reducedCenterObj M) I =>
      f.hom x)
    (TauCeti.CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom e I hI)
  exact h

theorem sigmaConnectedCenter_cube
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (σ : M →ₐc[k] M) (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) :
    ((sigmaConnectedCenter M σ hσ3).comp (sigmaConnectedCenter M σ hσ3)).comp
        (sigmaConnectedCenter M σ hσ3) = BialgHom.id k (connectedCenter M) := by
  let : Algebra.FiniteType k (reducedCenterObj M) := inferInstance
  let I := TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := reducedCenterObj M)
  apply BialgHom.ext
  intro y
  obtain ⟨x, rfl⟩ := TauCeti.CommHopfAlgCat.mkQuotient_surjective
    (reducedCenterObj M) I y
  rw [BialgHom.comp_apply, BialgHom.comp_apply, BialgHom.id_apply]
  rw [sigmaConnectedCenter_apply_mk M σ hσ3,
    sigmaConnectedCenter_apply_mk M σ hσ3,
    sigmaConnectedCenter_apply_mk M σ hσ3]
  have hcube : sigmaReducedCenter M σ hσ3
      (sigmaReducedCenter M σ hσ3 (sigmaReducedCenter M σ hσ3 x)) = x := by
    simpa only [BialgHom.comp_apply, BialgHom.id_apply] using
      congrArg (fun f : reducedCenterObj M →ₐc[k] reducedCenterObj M => f x)
        (sigmaReducedCenter_cube M σ hσ3)
  rw [hcube]

theorem sigmaConnectedCenter_comp_coordinateMap
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σ : M →ₐc[k] M) (hσ : (σ.comp σ).comp σ = BialgHom.id k M) :
    (sigmaConnectedCenter M σ hσ).comp (connectedCenterCoordinateMap M) =
      (connectedCenterCoordinateMap M).comp σ := by
  apply BialgHom.ext
  intro x
  let c := (TauCeti.CommHopfAlgCat.mkQuotient M.obj
    (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj)).hom
  let r := (TauCeti.CommHopfAlgCat.mkQuotient (centerObj M) (centerReductionIdeal M)).hom
  let z := (TauCeti.CommHopfAlgCat.mkQuotient (reducedCenterObj M)
    (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H :=
      TauCeti.FiniteTypeCommHopfAlgCat.of k (reducedCenterObj M)))).hom
  change sigmaConnectedCenter M σ hσ (z (r (c x))) = z (r (c (σ x)))
  rw [sigmaConnectedCenter_apply_mk, sigmaReducedCenter_apply_mk, centerIso_apply_mk,
    autIso_hom_hom]

end Core

theorem isCentralPoint_mapDomain_of_surjective_points
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced M]
    (σ : M →ₐc[k] M)
    (hσ : Function.Surjective (TauCeti.AlgHom.mapDomain (A := k) σ))
    (z : TauCeti.HopfAlgebra.points (R := k) (H := M) (CommAlgCat.of k k))
    (hz : TauCeti.HopfAlgebra.IsCentralPoint z) :
    TauCeti.HopfAlgebra.IsCentralPoint (TauCeti.AlgHom.mapDomain σ z) := by
  apply isCentralPoint_of_commute_base_points M
  intro p
  obtain ⟨s, hs⟩ := hσ p
  have he : TauCeti.AlgHom.mapValue (Algebra.ofId k k) p = p := by
    apply WithConv.ofConv_injective
    ext a
    rw [TauCeti.AlgHom.mapValue_apply]
    exact (Algebra.ofId k k).commutes (p.ofConv a)
  rw [he, ← hs]
  exact (hz.commute s).map (TauCeti.AlgHom.mapDomain σ)

theorem connectedCenter_mapDomain_central
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced M]
    (σ : M →ₐc[k] M)
    (hσ : Function.Surjective (TauCeti.AlgHom.mapDomain (A := k) σ))
    (z : TauCeti.HopfAlgebra.points (R := k) (H := connectedCenter M) (CommAlgCat.of k k)) :
    TauCeti.HopfAlgebra.IsCentralPoint
      (TauCeti.AlgHom.mapDomain ((connectedCenterCoordinateMap M).comp σ) z) := by
  rw [TauCeti.AlgHom.mapDomain_comp, MonoidHom.comp_apply]
  apply isCentralPoint_mapDomain_of_surjective_points M σ hσ
  exact CentralProduct.pointImageCentral_of_isCentral_ker
    (connectedCenterCoordinateMap M) (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj)
    (TauCeti.CommHopfAlgCat.isCentral_centerDefiningIdeal M.obj)
    (connectedCenterCoordinateMap_kills_centerDefiningIdeal M) _ z

theorem exists_connectedCenterEnd
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (σ : M →ₐc[k] M)
    (hσ : Function.Surjective (TauCeti.AlgHom.mapDomain (A := k) σ)) :
    ∃ τ : connectedCenter M →ₐc[k] connectedCenter M,
      τ.comp (connectedCenterCoordinateMap M) = (connectedCenterCoordinateMap M).comp σ := by
  let T := connectedCenter M
  let : Algebra.Smooth k M := hM.smooth
  let : IsReduced M := TauCeti.isReduced_of_smooth k M
  let : Algebra.Smooth k T := (reductive_connectedCenter M hM).smooth
  let : IsReduced T := TauCeti.isReduced_of_smooth k T
  let : ConnectedSpace (PrimeSpectrum T) :=
    TauCeti.FiniteTypeCommHopfAlgCat.connectedSpace_identityComponent _
  let c := (connectedCenterCoordinateMap M).comp σ
  have hcenter : (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj).toIdeal ≤
      RingHom.ker c.toAlgHom.toRingHom := by
    intro a ha
    change c a = 0
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
    intro p
    have hz := connectedCenter_mapDomain_central M σ hσ (toConv p)
    have hmem := (TauCeti.CommHopfAlgCat.mem_centerPointsSubgroup_iff M.obj _ _).2 hz
    have h := (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff M.obj _ _ _).1 hmem a ha
    rw [TauCeti.AlgHom.mapDomain_apply_apply] at h
    exact h.trans (map_zero p).symm
  exact exists_connectedCenter_lift M T c hcenter

end CFSG.LieType.AlgebraicGroups.CanonicalReductive
