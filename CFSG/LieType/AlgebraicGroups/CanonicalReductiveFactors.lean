module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Center.Reduced
public import TauCeti.Algebra.AlgebraicGroup.Smooth.IdentityComponent
public import TauCeti.RingTheory.FiniteType.Tensor.Product
public import TauCeti.Algebra.AlgebraicGroup.Derived.Connected
public import TauCeti.Algebra.AlgebraicGroup.Derived.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Derived.Functoriality

public noncomputable section

open CategoryTheory
namespace CFSG.LieType.AlgebraicGroups.CanonicalReductive
universe u
variable {k : Type u} [Field k]

theorem reductive_quotient_of_isCentral
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : I.IsCentral)
    (hsm : Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I))
    (hconn : TauCeti.geometricallyConnectedCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I).obj) :
    TauCeti.reductiveCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I) := by
  rw [TauCeti.reductiveCommHopfAlgProperty_iff]
  refine ⟨hsm, hconn, ?_⟩
  intro J hJ hJconn hJU
  let Mbar := TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) M
  let Qbar := TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
    (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I)
  let Ibar := TauCeti.CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) I
  let e := TauCeti.CommHopfAlgCat.quotientBaseChangeIso (K := AlgebraicClosure k) I
  let π : Mbar.obj ⟶ Qbar.obj :=
    TauCeti.CommHopfAlgCat.mkQuotient Mbar.obj Ibar ≫ e.hom
  have hπ : Function.Surjective π.hom :=
    (ConcreteCategory.bijective_of_isIso e.hom).2.comp
      (TauCeti.CommHopfAlgCat.mkQuotient_surjective Mbar.obj Ibar)
  let K := J.comapOfSurjective π.hom hπ
  have hIK : Ibar ≤ K := by
    intro x hx
    rw [TauCeti.HopfIdeal.mem_comapOfSurjective]
    have hzero := (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff Mbar.obj Ibar x).2 hx
    change e.hom.hom ((TauCeti.CommHopfAlgCat.mkQuotient Mbar.obj Ibar).hom x) ∈ J
    rw [hzero, map_zero]
    exact J.toIdeal.zero_mem
  have hKcentral : K.IsCentral :=
    (TauCeti.CommHopfAlgCat.isCentral_baseChangeHopfIdeal hI).mono hIK
  let eK := TauCeti.CommHopfAlgCat.quotientIsoOfSurjective π hπ J
  let eKft : TauCeti.FiniteTypeCommHopfAlgCat.quotient Mbar K ≅
      TauCeti.FiniteTypeCommHopfAlgCat.quotient Qbar J :=
    ObjectProperty.isoMk (TauCeti.finiteTypeCommHopfAlgProperty (AlgebraicClosure k)) eK
  have hKconn : TauCeti.geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient Mbar K).obj :=
    (TauCeti.geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
      eK.symm hJconn
  have hKU : TauCeti.smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k)
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient Mbar K) :=
    (TauCeti.smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
      eKft.symm hJU
  have hK := hM.eq_augmentation K hKcentral.isNormal hKconn hKU
  apply (TauCeti.HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff π.hom hπ).mp
  rw [TauCeti.HopfIdeal.comapOfSurjective_augmentation]
  exact hK


variable [IsAlgClosed k]

abbrev connectedCenter (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :=
  TauCeti.FiniteTypeCommHopfAlgCat.identityComponent
    (TauCeti.FiniteTypeCommHopfAlgCat.of k
      (TauCeti.CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra M.obj))

abbrev connectedCenterCoordinateMap (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    M →ₐc[k] connectedCenter M :=
  ((TauCeti.CommHopfAlgCat.mkQuotient
      (TauCeti.CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra M.obj)
      (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k)
        (H := TauCeti.FiniteTypeCommHopfAlgCat.of k
          (TauCeti.CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra M.obj)))).hom.comp
    (TauCeti.CommHopfAlgCat.mkQuotient
      (TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra M.obj)
      (TauCeti.HopfIdeal.reduction k
        (TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra M.obj))).hom).comp
    (TauCeti.CommHopfAlgCat.mkQuotient M.obj
      (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj)).hom

theorem connectedCenterCoordinateMap_surjective
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    Function.Surjective (connectedCenterCoordinateMap M) :=
  (TauCeti.CommHopfAlgCat.mkQuotient_surjective
    (TauCeti.CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra M.obj)
    (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k)
      (H := TauCeti.FiniteTypeCommHopfAlgCat.of k
        (TauCeti.CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra M.obj)))).comp
    ((TauCeti.CommHopfAlgCat.mkQuotient_surjective
      (TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra M.obj)
      (TauCeti.HopfIdeal.reduction k
        (TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra M.obj))).comp
      (TauCeti.CommHopfAlgCat.mkQuotient_surjective M.obj
        (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj)))

theorem exists_connectedCenter_lift
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (P : Type u) [CommRing P] [HopfAlgebra k P]
    [IsReduced P] [ConnectedSpace (PrimeSpectrum P)]
    (f : M →ₐc[k] P)
    (hf : ∀ a ∈ TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj, f a = 0) :
    ∃ fZ : connectedCenter M →ₐc[k] P,
      fZ.comp (connectedCenterCoordinateMap M) = f := by
  let C := TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra M.obj
  let R := TauCeti.CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra M.obj
  have hcenter : (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj).toIdeal ≤
      RingHom.ker f.toAlgHom.toRingHom := hf
  let fC : C ⟶ _root_.CommHopfAlgCat.of k P := TauCeti.CommHopfAlgCat.liftQuotient
    (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj) (_root_.CommHopfAlgCat.ofHom f) hcenter
  have hred : (TauCeti.HopfIdeal.reduction k C).toIdeal ≤
      RingHom.ker fC.hom.toAlgHom.toRingHom := by
    intro a ha
    exact ((TauCeti.HopfIdeal.mem_reduction k C).1 ha).map fC.hom |>.eq_zero
  let fR : R ⟶ _root_.CommHopfAlgCat.of k P := TauCeti.CommHopfAlgCat.liftQuotient
    (TauCeti.HopfIdeal.reduction k C) fC hred
  have hconn : (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := R)).toIdeal ≤
      RingHom.ker fR.hom.toAlgHom.toRingHom :=
    TauCeti.CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected fR
  let fZ : (connectedCenter M).obj ⟶ _root_.CommHopfAlgCat.of k P :=
    TauCeti.CommHopfAlgCat.liftQuotient
      (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := R)) fR hconn
  refine ⟨fZ.hom, ?_⟩
  have heC := TauCeti.CommHopfAlgCat.mkQuotient_comp_liftQuotient
    (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj) (_root_.CommHopfAlgCat.ofHom f) hcenter
  have heR := TauCeti.CommHopfAlgCat.mkQuotient_comp_liftQuotient
    (TauCeti.HopfIdeal.reduction k C) fC hred
  have heZ := TauCeti.CommHopfAlgCat.mkQuotient_comp_liftQuotient
    (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := R)) fR hconn
  change (fZ.hom.comp (TauCeti.CommHopfAlgCat.mkQuotient R _).hom).comp
      ((TauCeti.CommHopfAlgCat.mkQuotient C _).hom.comp
        (TauCeti.CommHopfAlgCat.mkQuotient M.obj _).hom) = f
  have hz : fZ.hom.comp (TauCeti.CommHopfAlgCat.mkQuotient R _).hom = fR.hom :=
    congrArg (fun q => q.hom) heZ
  have hr : fR.hom.comp (TauCeti.CommHopfAlgCat.mkQuotient C _).hom = fC.hom :=
    congrArg (fun q => q.hom) heR
  have hc : fC.hom.comp (TauCeti.CommHopfAlgCat.mkQuotient M.obj _).hom = f :=
    congrArg (fun q => q.hom) heC
  rw [hz, ← BialgHom.comp_assoc, hr, hc]

theorem connectedCenterCoordinateMap_kills_centerDefiningIdeal
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    ∀ x ∈ TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj,
      connectedCenterCoordinateMap M x = 0 := by
  intro x hx
  have hzero := (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff M.obj
    (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj) x).2 hx
  change (TauCeti.CommHopfAlgCat.mkQuotient _ _).hom
    ((TauCeti.CommHopfAlgCat.mkQuotient _ _).hom
      ((TauCeti.CommHopfAlgCat.mkQuotient M.obj _).hom x)) = 0
  rw [hzero, map_zero, map_zero]

theorem reductive_connectedCenter
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M) :
    TauCeti.reductiveCommHopfAlgProperty k (connectedCenter M) := by
  let q := _root_.CommHopfAlgCat.ofHom (connectedCenterCoordinateMap M)
  let hq := connectedCenterCoordinateMap_surjective M
  let I := TauCeti.HopfIdeal.kerOfSurjective q.hom hq
  have hCI : TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj ≤ I := by
    intro x hx
    rw [TauCeti.HopfIdeal.mem_kerOfSurjective]
    exact connectedCenterCoordinateMap_kills_centerDefiningIdeal M x hx
  let e := TauCeti.CommHopfAlgCat.quotientKerOfSurjectiveIso q hq
  let eft : TauCeti.FiniteTypeCommHopfAlgCat.quotient M I ≅ connectedCenter M :=
    ObjectProperty.isoMk (TauCeti.finiteTypeCommHopfAlgProperty k) e
  let Rft := TauCeti.FiniteTypeCommHopfAlgCat.of k
    (TauCeti.CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra M.obj)
  let : Algebra.Smooth k Rft := TauCeti.CommHopfAlgCat.smooth_reducedCenterCoordinateHopfAlgebra M.obj
  have hzsm : Algebra.Smooth k (connectedCenter M) :=
    TauCeti.FiniteTypeCommHopfAlgCat.smooth_identityComponent Rft
  have hzconn : TauCeti.geometricallyConnectedCommHopfAlgProperty k (connectedCenter M).obj :=
    TauCeti.FiniteTypeCommHopfAlgCat.geometricallyConnected_identityComponent Rft
  have hIsm : Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I) :=
    (TauCeti.smoothCommHopfAlgProperty_iff _).mp
      ((TauCeti.smoothCommHopfAlgProperty k).prop_of_iso e.symm
        ((TauCeti.smoothCommHopfAlgProperty_iff _).mpr hzsm))
  have hIconn := (TauCeti.geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm hzconn
  exact (TauCeti.reductiveCommHopfAlgProperty k).prop_of_iso eft
    (reductive_quotient_of_isCentral M hM I
      ((TauCeti.CommHopfAlgCat.isCentral_centerDefiningIdeal M.obj).mono hCI) hIsm hIconn)

abbrev derivedCoordinate (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k :=
  TauCeti.FiniteTypeCommHopfAlgCat.quotient M
    (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) M)

theorem smooth_geometricallyConnected_derivedCoordinate
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M) :
    Algebra.Smooth k (derivedCoordinate M) ∧
      TauCeti.geometricallyConnectedCommHopfAlgProperty k (derivedCoordinate M).obj := by
  let : Algebra.Smooth k M := hM.smooth
  let : IsReduced M := TauCeti.isReduced_of_smooth k M
  let : ConnectedSpace (PrimeSpectrum M) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace k M.obj hM.geometricallyConnected
  refine ⟨?_, TauCeti.CommHopfAlgCat.geometricallyConnectedCommHopfAlgProperty_derived M⟩
  exact (TauCeti.smoothCommHopfAlgProperty_iff _).mp
    (TauCeti.CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_derivedDefiningIdeal M.obj)


abbrev derivedCoordinateMap (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    M →ₐc[k] derivedCoordinate M :=
  (TauCeti.CommHopfAlgCat.mkQuotient M.obj
    (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) M)).hom

def derivedCoordinateEnd (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σ : M →ₐc[k] M) : derivedCoordinate M →ₐc[k] derivedCoordinate M :=
  (TauCeti.CommHopfAlgCat.derivedMap (_root_.CommHopfAlgCat.ofHom σ)).hom

omit [IsAlgClosed k] in
theorem derivedCoordinateEnd_comp (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σ : M →ₐc[k] M) :
    (derivedCoordinateEnd M σ).comp (derivedCoordinateMap M) =
      (derivedCoordinateMap M).comp σ := by
  have h := TauCeti.CommHopfAlgCat.mkQuotient_comp_derivedMap (_root_.CommHopfAlgCat.ofHom σ)
  exact congrArg (fun f => f.hom) h

omit [IsAlgClosed k] in
theorem derivedCoordinateEnd_cube (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σ : M →ₐc[k] M) (hσ : (σ.comp σ).comp σ = BialgHom.id k M) :
    ((derivedCoordinateEnd M σ).comp (derivedCoordinateEnd M σ)).comp
      (derivedCoordinateEnd M σ) = BialgHom.id k (derivedCoordinate M) := by
  apply BialgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := TauCeti.CommHopfAlgCat.mkQuotient_surjective M.obj
    (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) M) x
  have hcomp : ∀ a, derivedCoordinateEnd M σ (derivedCoordinateMap M a) =
      derivedCoordinateMap M (σ a) := fun a =>
    congrArg (fun f : M →ₐc[k] derivedCoordinate M => f a) (derivedCoordinateEnd_comp M σ)
  change derivedCoordinateEnd M σ
    (derivedCoordinateEnd M σ (derivedCoordinateEnd M σ (derivedCoordinateMap M a))) =
    derivedCoordinateMap M a
  rw [hcomp, hcomp, hcomp]
  exact congrArg (derivedCoordinateMap M) (congrArg (fun f : M →ₐc[k] M => f a) hσ)

omit [IsAlgClosed k] in
theorem comp_comm_of_restrictions_of_surjective
    (D T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D →ₐc[k] T) (hq : Function.Surjective q)
    (F σ : D →ₐc[k] D) (FT σT : T →ₐc[k] T)
    (hF : FT.comp q = q.comp F) (hσ : σT.comp q = q.comp σ)
    (hcomm : F.comp σ = σ.comp F) : FT.comp σT = σT.comp FT := by
  apply BialgHom.ext
  intro x
  obtain ⟨a,rfl⟩ := hq x
  have hFe (a : D) : FT (q a) = q (F a) :=
    congrArg (fun f : D →ₐc[k] T => f a) hF
  have hσe (a : D) : σT (q a) = q (σ a) :=
    congrArg (fun f : D →ₐc[k] T => f a) hσ
  change FT (σT (q a)) = σT (FT (q a))
  rw [hσe,hFe,hFe,hσe]
  exact congrArg q (congrArg (fun f : D →ₐc[k] D => f a) hcomm)


omit [IsAlgClosed k] in
theorem derivedCoordinateEnd_comp_eq_comp
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (F σ : M →ₐc[k] M) (hcomm : F.comp σ = σ.comp F) :
    (derivedCoordinateEnd M F).comp (derivedCoordinateEnd M σ) =
      (derivedCoordinateEnd M σ).comp (derivedCoordinateEnd M F) := by
  apply comp_comm_of_restrictions_of_surjective M (derivedCoordinate M)
    (derivedCoordinateMap M) (TauCeti.CommHopfAlgCat.mkQuotient_surjective M.obj _) F σ
    _ _ (derivedCoordinateEnd_comp M F) (derivedCoordinateEnd_comp M σ) hcomm


end CFSG.LieType.AlgebraicGroups.CanonicalReductive
