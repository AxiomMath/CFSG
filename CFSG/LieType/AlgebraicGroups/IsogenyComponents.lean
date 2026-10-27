module

public import CFSG.LieType.AlgebraicGroups.CentralProductMorphism
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FiniteFlat
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Reduction
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Image
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Reduced
public import TauCeti.RingTheory.FiniteType.FiniteRange
public import TauCeti.RingTheory.Spectrum.Prime.Topology
public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange

public noncomputable section
open CategoryTheory WithConv
open scoped TensorProduct
namespace CFSG.LieType.AlgebraicGroups.Isogeny
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem isOpenMap_comap_of_isogeny
    (H X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (f : H.obj ⟶ X.obj) (hf : TauCeti.CommHopfAlgCat.IsIsogeny f) :
    IsOpenMap (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom) := by
  let := f.hom.toAlgHom.toAlgebra
  let : Module.Finite H X := hf.finite
  let : Module.Flat H X := hf.faithfullyFlat.flat
  let : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let : Algebra.FiniteType H X := inferInstance
  let : Algebra.FinitePresentation H X := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.HasGoingDown H X := Algebra.HasGoingDown.of_flat
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

omit [IsAlgClosed k] in
theorem image_connectedComponent_augmentation_eq_univ_of_isogeny
    (H X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (f : H.obj ⟶ X.obj) (hf : TauCeti.CommHopfAlgCat.IsIsogeny f)
    [ConnectedSpace (PrimeSpectrum H)] :
    PrimeSpectrum.comap f.hom.toAlgHom.toRingHom ''
      connectedComponent (TauCeti.Bialgebra.augmentationPoint k X) = Set.univ := by
  let : IsNoetherianRing X := Algebra.FiniteType.isNoetherianRing k X
  let : LocallyConnectedSpace (PrimeSpectrum X) := inferInstance
  have hc : IsClopen (connectedComponent (TauCeti.Bialgebra.augmentationPoint k X)) :=
    isClopen_connectedComponent
  have hopen := isOpenMap_comap_of_isogeny H X f hf
  have hclosed : IsClosedMap (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom) :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (RingHom.Finite.to_isIntegral hf.finite)
  apply IsClopen.eq_univ ⟨hclosed _ hc.isClosed, hopen _ hc.isOpen⟩
  exact Set.Nonempty.image _ ⟨TauCeti.Bialgebra.augmentationPoint k X, mem_connectedComponent⟩

theorem isIsogeny_comp_identityComponent
    (H X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (f : H.obj ⟶ X.obj) (hf : TauCeti.CommHopfAlgCat.IsIsogeny f)
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)] :
    TauCeti.CommHopfAlgCat.IsIsogeny
      (f ≫ TauCeti.CommHopfAlgCat.mkQuotient X.obj
        (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := X))) := by
  let : IsNoetherianRing X := Algebra.FiniteType.isNoetherianRing k X
  let : LocallyConnectedSpace (PrimeSpectrum X) := inferInstance
  let j := TauCeti.CommHopfAlgCat.mkQuotient X.obj
    (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := X))
  let g := f ≫ j
  have hfin : g.hom.toAlgHom.Finite :=
    AlgHom.Finite.comp (RingHom.Finite.of_surjective _
      (TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _)) hf.finite
  have hsurj : Function.Surjective (PrimeSpectrum.comap g.hom.toAlgHom.toRingHom) := by
    intro p
    have hp : p ∈ PrimeSpectrum.comap f.hom.toAlgHom.toRingHom ''
        connectedComponent (TauCeti.Bialgebra.augmentationPoint k X) := by
      rw [image_connectedComponent_augmentation_eq_univ_of_isogeny H X f hf]
      exact Set.mem_univ _
    obtain ⟨x, hx, hxp⟩ := hp
    let I := TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := X)
    let e := PrimeSpectrum.quotientHomeomorphZeroLocus I.toIdeal
    have hxI : x ∈ PrimeSpectrum.zeroLocus (I.toIdeal : Set X) := by
      change x ∈ PrimeSpectrum.zeroLocus
        ((TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := X)).toIdeal : Set X)
      rw [TauCeti.HopfAlgebra.identityComponentHopfIdeal_toIdeal]
      change x ∈ PrimeSpectrum.zeroLocus
        (PrimeSpectrum.connectedComponentIdeal
          (show PrimeSpectrum X from TauCeti.Bialgebra.augmentationPoint k X) : Set X)
      rw [PrimeSpectrum.zeroLocus_connectedComponentIdeal]
      exact hx
    let t : PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent X) :=
      e.symm ⟨x, hxI⟩
    have ht : PrimeSpectrum.comap j.hom.toAlgHom.toRingHom t = x := by
      change PrimeSpectrum.comap (Ideal.Quotient.mk I.toIdeal) t = x
      rw [← PrimeSpectrum.quotientHomeomorphZeroLocus_apply_coe I.toIdeal t]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hxI⟩)
    refine ⟨t, ?_⟩
    change PrimeSpectrum.comap (j.hom.comp f.hom).toAlgHom.toRingHom t = p
    change PrimeSpectrum.comap (j.hom.toAlgHom.toRingHom.comp f.hom.toAlgHom.toRingHom) t = p
    rw [PrimeSpectrum.comap_comp, Function.comp_apply]
    exact (congrArg (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom) ht).trans hxp
  apply (TauCeti.CommHopfAlgCat.isIsogeny_iff _).2
  exact ⟨hfin, TauCeti.CommHopfAlgCat.faithfullyFlat_of_finite_of_dominant g hfin hsurj.denseRange⟩

omit [IsAlgClosed k] in
theorem isCentral_kernel_comp_surjective
    (H X Y : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (f : H.obj ⟶ X.obj) (hf : (TauCeti.CommHopfAlgCat.kernelHopfIdeal f).IsCentral)
    (j : X.obj ⟶ Y.obj) (hj : Function.Surjective j.hom) :
    (TauCeti.CommHopfAlgCat.kernelHopfIdeal (f ≫ j)).IsCentral := by
  apply (TauCeti.CommHopfAlgCat.isCentral_iff_forall_isCentralPoint _ _).2
  intro A y hy
  have heq : TauCeti.AlgHom.mapDomain f.hom (TauCeti.AlgHom.mapDomain j.hom y) = 1 := by
    rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp]
    exact (TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff (f ≫ j) A y).2 hy
  have hyc : TauCeti.HopfAlgebra.IsCentralPoint (TauCeti.AlgHom.mapDomain j.hom y) :=
    TauCeti.CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup _ _ hf A
      ((TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff f A _).1 heq)
  exact CFSG.LieType.AlgebraicGroups.CentralProduct.isCentralPoint_of_mapDomain_of_surjective
    j.hom hj y hyc

theorem isCentralIsogeny_comp_identityComponent
    (H X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (f : H.obj ⟶ X.obj) (hf : TauCeti.CommHopfAlgCat.IsCentralIsogeny f)
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)] :
    TauCeti.CommHopfAlgCat.IsCentralIsogeny
      (f ≫ TauCeti.CommHopfAlgCat.mkQuotient X.obj
        (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := X))) := by
  apply (TauCeti.CommHopfAlgCat.isCentralIsogeny_iff _).2
  have hi := isIsogeny_comp_identityComponent H X f hf.isIsogeny
  exact ⟨hi.finite, hi.faithfullyFlat,
    isCentral_kernel_comp_surjective H X
      (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent X) f hf.isCentral_kernelHopfIdeal
      (TauCeti.CommHopfAlgCat.mkQuotient X.obj
        (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := X)))
      (TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _)⟩

theorem smooth_quotient_reduction
    (X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.quotient X
      (TauCeti.HopfIdeal.reduction k X)) :=
  (TauCeti.smoothCommHopfAlgProperty_iff _).mp
    (TauCeti.smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient X (TauCeti.HopfIdeal.reduction k X)).obj)

theorem isIsogeny_comp_reduction
    (H X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (f : H.obj ⟶ X.obj) (hf : TauCeti.CommHopfAlgCat.IsIsogeny f)
    [IsReduced H] :
    TauCeti.CommHopfAlgCat.IsIsogeny
      (f ≫ TauCeti.CommHopfAlgCat.mkQuotient X.obj (TauCeti.HopfIdeal.reduction k X)) := by
  let j := TauCeti.CommHopfAlgCat.mkQuotient X.obj (TauCeti.HopfIdeal.reduction k X)
  let g := f ≫ j
  have hfin : g.hom.toAlgHom.Finite := AlgHom.Finite.comp
    (RingHom.Finite.of_surjective _ (TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _)) hf.finite
  have hinj : Function.Injective g.hom := by
    intro a b hab
    have hab' : j.hom (f.hom a) = j.hom (f.hom b) := hab
    have hab0 : j.hom (f.hom (a - b)) = 0 := by
      rw [map_sub, map_sub, hab', sub_self]
    have hn : IsNilpotent (f.hom (a - b)) :=
      (TauCeti.HopfIdeal.mem_reduction k X).1
        ((TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff X.obj
          (TauCeti.HopfIdeal.reduction k X) _).1 hab0)
    obtain ⟨n, hn⟩ := hn
    have ha : (a - b) ^ n = 0 := hf.injective (by rw [map_pow, hn, map_zero])
    exact sub_eq_zero.mp ((show IsNilpotent (a - b) from ⟨n, ha⟩).eq_zero)
  apply (TauCeti.CommHopfAlgCat.isIsogeny_iff _).2
  exact ⟨hfin, TauCeti.CommHopfAlgCat.faithfullyFlat_of_finite_of_dominant
    g hfin (RingHom.denseRange_comap_of_injective _ hinj)⟩

theorem isCentralIsogeny_comp_reduction
    (H X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (f : H.obj ⟶ X.obj) (hf : TauCeti.CommHopfAlgCat.IsCentralIsogeny f)
    [IsReduced H] :
    TauCeti.CommHopfAlgCat.IsCentralIsogeny
      (f ≫ TauCeti.CommHopfAlgCat.mkQuotient X.obj (TauCeti.HopfIdeal.reduction k X)) := by
  apply (TauCeti.CommHopfAlgCat.isCentralIsogeny_iff _).2
  have hi := isIsogeny_comp_reduction H X f hf.isIsogeny
  exact ⟨hi.finite, hi.faithfullyFlat,
    isCentral_kernel_comp_surjective H X
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient X (TauCeti.HopfIdeal.reduction k X))
      f hf.isCentral_kernelHopfIdeal
      (TauCeti.CommHopfAlgCat.mkQuotient X.obj (TauCeti.HopfIdeal.reduction k X))
      (TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _)⟩


omit [IsAlgClosed k] in
theorem finite_baseChangeMap
    (H X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (f : H.obj ⟶ X.obj) (hf : f.hom.toAlgHom.Finite)
    (K : Type u) [Field K] [Algebra k K] :
    (TauCeti.CommHopfAlgCat.baseChangeMap (K := K) f).hom.toAlgHom.Finite := by
  have ht := RingHom.Finite.tensorProductMap
    (AlgHom.Finite.id k K) hf
  exact ht

omit [IsAlgClosed k] in
theorem semisimple_of_finite_of_injective
    (H X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hH : TauCeti.semisimpleCommHopfAlgProperty k H)
    (f : H.obj ⟶ X.obj) (hf : f.hom.toAlgHom.Finite)
    (hfi : Function.Injective f.hom)
    (hsm : Algebra.Smooth k X)
    (hc : TauCeti.geometricallyConnectedCommHopfAlgProperty k X.obj) :
    TauCeti.semisimpleCommHopfAlgProperty k X := by
  rw [TauCeti.semisimpleCommHopfAlgProperty_iff]
  refine ⟨hsm, hc, ?_⟩
  intro I hIn hIc hIs hIv
  let Hbar := TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
  let Xbar := TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) X
  let fb : Hbar.obj ⟶ Xbar.obj := TauCeti.CommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k) f
  have hfbi : Function.Injective fb.hom := TauCeti.CommHopfAlgCat.baseChangeMap_injective f hfi
  let : Module.Flat (AlgebraicClosure k) Hbar := Module.Flat.of_free
  let : Module.Flat (AlgebraicClosure k) (Xbar ⧸ I.toIdeal) := Module.Flat.of_free
  let : Module.Flat (AlgebraicClosure k)
      (Hbar ⧸ Ideal.comap (fb.hom : Hbar →+* Xbar) I.toIdeal) := Module.Flat.of_free
  let J := I.comap fb.hom
  have hJn : J.IsNormal := hIn.comap_of_injective fb.hom hfbi
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient Xbar I
  let g : Hbar.obj ⟶ Q.obj := fb ≫ TauCeti.CommHopfAlgCat.mkQuotient Xbar.obj I
  let : Module.Flat (AlgebraicClosure k)
      (Hbar ⧸ RingHom.ker g.hom.toAlgHom) := Module.Flat.of_free
  have hJker : J = TauCeti.HopfIdeal.ker g.hom := by
    ext a
    rw [TauCeti.HopfIdeal.mem_comap, TauCeti.HopfIdeal.mem_ker]
    change fb.hom a ∈ I ↔ (TauCeti.CommHopfAlgCat.mkQuotient Xbar.obj I).hom (fb.hom a) = 0
    exact (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff Xbar.obj I (fb.hom a)).symm
  have hJc : TauCeti.geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient Hbar J).obj := by
    rw [hJker]
    exact TauCeti.geometricallyConnectedCommHopfAlgProperty.image g hIc
  have hJs : Algebra.Smooth (AlgebraicClosure k)
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient Hbar J) := by
    rw [hJker]
    exact (TauCeti.smoothCommHopfAlgProperty_iff _).mp
      (TauCeti.smoothCommHopfAlgProperty.image g
        ((TauCeti.smoothCommHopfAlgProperty_iff _).mpr hIs))
  have hJv : TauCeti.geometricallySolvablePointsCommHopfAlgProperty (AlgebraicClosure k)
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient Hbar J).obj := by
    rw [hJker]
    exact TauCeti.geometricallySolvablePointsCommHopfAlgProperty.of_injective_of_smooth
      (TauCeti.CommHopfAlgCat.imageι g) (TauCeti.CommHopfAlgCat.imageι_injective g) hIs hIv
  have hJ := hH.eq_augmentation J hJn hJc hJs hJv
  have hkernel : TauCeti.CommHopfAlgCat.kernelHopfIdeal fb ≤ I := by
    rw [TauCeti.CommHopfAlgCat.kernelHopfIdeal_def]
    apply TauCeti.HopfIdeal.map_le_iff.2
    intro a ha
    have haJ : a ∈ J := hJ.symm ▸ ha
    exact TauCeti.HopfIdeal.mem_comap.1 haJ
  let K := TauCeti.CommHopfAlgCat.quotient Xbar.obj (TauCeti.CommHopfAlgCat.kernelHopfIdeal fb)
  let : Module.Finite (AlgebraicClosure k) K :=
    TauCeti.CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal
      (finite_baseChangeMap H X f hf (AlgebraicClosure k))
  let q : K ⟶ Q.obj := TauCeti.CommHopfAlgCat.quotientMapOfLe Xbar.obj hkernel
  let : Module.Finite (AlgebraicClosure k) Q := Module.Finite.of_surjective
    q.hom.toAlgHom.toLinearMap (TauCeti.CommHopfAlgCat.quotientMapOfLe_surjective Xbar.obj hkernel)
  let : Algebra.Smooth (AlgebraicClosure k) Q := hIs
  let : IsReduced Q := TauCeti.isReduced_of_smooth (AlgebraicClosure k) Q
  let : ConnectedSpace (PrimeSpectrum Q) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace (AlgebraicClosure k) Q.obj hIc
  apply le_antisymm
  · exact TauCeti.HopfIdeal.le_augmentation _ _ _
  · intro a ha
    have hconst := TauCeti.eq_algebraMap_of_finite_range_eval
      ((TauCeti.CommHopfAlgCat.mkQuotient Xbar.obj I).hom a) (Set.finite_range _)
      (Bialgebra.counitAlgHom (AlgebraicClosure k) Q)
    have hca : Bialgebra.counitAlgHom (AlgebraicClosure k) Q
        ((TauCeti.CommHopfAlgCat.mkQuotient Xbar.obj I).hom a) = 0 := by
      have he := AlgHom.congr_fun (BialgHom.counitAlgHom_comp
        (TauCeti.CommHopfAlgCat.mkQuotient Xbar.obj I).hom) a
      exact he.trans ((TauCeti.HopfIdeal.mem_augmentation _ _).1 ha)
    rw [hca, map_zero] at hconst
    exact (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff Xbar.obj I a).1 hconst

end CFSG.LieType.AlgebraicGroups.Isogeny
