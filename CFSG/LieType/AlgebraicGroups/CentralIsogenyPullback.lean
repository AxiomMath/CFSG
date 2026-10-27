module

public import CFSG.LieType.AlgebraicGroups.CentralProductMorphism
public import CFSG.LieType.AlgebraicGroups.TensorCentralIsogeny
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FiniteFlat
public import TauCeti.RingTheory.Spectrum.Prime.Topology

public noncomputable section
open CategoryTheory WithConv
open scoped TensorProduct
namespace CFSG.LieType.AlgebraicGroups.CentralIsogenyPullback
universe u
variable {k : Type u} [Field k]

def leftToProduct (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (σ : D →ₐc[k] D) :
    D.obj ⟶ (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct S S).obj :=
  _root_.CommHopfAlgCat.ofHom
    ((TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft S S)).comp (q.hom.comp σ))

def rightToProduct (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) :
    D.obj ⟶ (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct S S).obj :=
  _root_.CommHopfAlgCat.ofHom
    ((TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.includeRight S S)).comp q.hom)

abbrev pullbackCoordinate (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (σ : D →ₐc[k] D) :
    TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k :=
  TauCeti.FiniteTypeCommHopfAlgCat.quotient
    (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct S S)
    (TauCeti.CommHopfAlgCat.equalizerHopfIdeal (leftToProduct D S q σ) (rightToProduct D S q))

abbrev pullbackQuotientMap (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (σ : D →ₐc[k] D) :
    (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct S S).obj ⟶
      (pullbackCoordinate D S q σ).obj :=
  TauCeti.CommHopfAlgCat.mkQuotient
    (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct S S).obj
    (TauCeti.CommHopfAlgCat.equalizerHopfIdeal (leftToProduct D S q σ) (rightToProduct D S q))

abbrev firstProjection (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (σ : D →ₐc[k] D) :
    S.obj ⟶ (pullbackCoordinate D S q σ).obj :=
  (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft S S).hom ≫ pullbackQuotientMap D S q σ

abbrev secondProjection (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (σ : D →ₐc[k] D) :
    S.obj ⟶ (pullbackCoordinate D S q σ).obj :=
  (TauCeti.FiniteTypeCommHopfAlgCat.includeRight S S).hom ≫ pullbackQuotientMap D S q σ

theorem projection_equation (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (σ : D →ₐc[k] D) :
    (firstProjection D S q σ).hom.comp (q.hom.comp σ) =
      (secondProjection D S q σ).hom.comp q.hom := by
  have h := TauCeti.CommHopfAlgCat.comp_mkQuotient_equalizerHopfIdeal
    (leftToProduct D S q σ) (rightToProduct D S q)
  exact congrArg (fun f => f.hom) h

theorem points_pullback_iff (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (σ : D →ₐc[k] D) (A : CommAlgCat.{u} k)
    (y : TauCeti.HopfAlgebra.points (R := k)
      (H := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct S S) A) :
    y ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup
      (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct S S).obj
      (TauCeti.CommHopfAlgCat.equalizerHopfIdeal (leftToProduct D S q σ) (rightToProduct D S q)) A ↔
      TauCeti.AlgHom.mapDomain (q.hom.comp σ)
          (TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A S S y).1 =
        TauCeti.AlgHom.mapDomain q.hom
          (TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A S S y).2 := by
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_equalizerHopfIdeal_iff]
  rw [CFSG.LieType.AlgebraicGroups.FixedProduct.pointsMulEquiv_fst_eq,
    CFSG.LieType.AlgebraicGroups.FixedProduct.pointsMulEquiv_snd_eq,
    ← MonoidHom.comp_apply, ← MonoidHom.comp_apply,
    ← TauCeti.AlgHom.mapDomain_comp, ← TauCeti.AlgHom.mapDomain_comp]
  rfl

theorem pullbackPoint_equation (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (σ : D →ₐc[k] D) (A : CommAlgCat.{u} k)
    (y : TauCeti.HopfAlgebra.points (R := k) (H := pullbackCoordinate D S q σ) A) :
    TauCeti.AlgHom.mapDomain (q.hom.comp σ)
        (TauCeti.AlgHom.mapDomain (firstProjection D S q σ).hom y) =
      TauCeti.AlgHom.mapDomain q.hom
        (TauCeti.AlgHom.mapDomain (secondProjection D S q σ).hom y) := by
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply,
    ← TauCeti.AlgHom.mapDomain_comp, ← TauCeti.AlgHom.mapDomain_comp,
    projection_equation]

theorem pullbackPoint_components (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (σ : D →ₐc[k] D) (A : CommAlgCat.{u} k)
    (y : TauCeti.HopfAlgebra.points (R := k) (H := pullbackCoordinate D S q σ) A) :
    TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A S S
        (TauCeti.AlgHom.mapDomain (pullbackQuotientMap D S q σ).hom y) =
      (TauCeti.AlgHom.mapDomain (firstProjection D S q σ).hom y,
        TauCeti.AlgHom.mapDomain (secondProjection D S q σ).hom y) := by
  apply Prod.ext
  · rw [FixedProduct.pointsMulEquiv_fst_eq,
      ← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp]
    rfl
  · rw [FixedProduct.pointsMulEquiv_snd_eq,
      ← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp]
    rfl

theorem isCentral_kernel_firstProjection (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (hq : TauCeti.CommHopfAlgCat.IsCentralIsogeny q)
    (σ : D →ₐc[k] D) :
    (TauCeti.CommHopfAlgCat.kernelHopfIdeal (firstProjection D S q σ)).IsCentral := by
  apply (TauCeti.CommHopfAlgCat.isCentral_iff_forall_isCentralPoint _ _).2
  intro A y hy
  have hfirst : TauCeti.AlgHom.mapDomain (firstProjection D S q σ).hom y = 1 :=
    (TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff _ A y).2 hy
  have hpair := pullbackPoint_components D S q σ A y
  have heq := pullbackPoint_equation D S q σ A y
  rw [hfirst, map_one] at heq
  have hsecond : TauCeti.HopfAlgebra.IsCentralPoint
      (TauCeti.AlgHom.mapDomain (secondProjection D S q σ).hom y) := by
    apply TauCeti.CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup _ _
      hq.isCentral_kernelHopfIdeal A
    exact (TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff q A _).1 heq.symm
  let i := (pullbackQuotientMap D S q σ).hom
  apply CentralProduct.isCentralPoint_of_mapDomain_of_surjective i
    (TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _) y
  apply CentralProduct.isCentralPoint_product_of_components S S
    (TauCeti.AlgHom.mapDomain i y)
  · rw [← pointsMulEquiv_eq_affine S S A, hpair, hfirst]
    exact TauCeti.HopfAlgebra.isCentralPoint_one
  · rw [← pointsMulEquiv_eq_affine S S A, hpair]
    exact hsecond

theorem firstProjection_surjective_points [IsAlgClosed k]
    (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (hq : TauCeti.CommHopfAlgCat.IsCentralIsogeny q)
    (σ : D →ₐc[k] D) :
    Function.Surjective (TauCeti.AlgHom.mapDomain (A := k) (firstProjection D S q σ).hom) := by
  let A := CommAlgCat.of k k
  intro s
  obtain ⟨t, ht⟩ := hq.isIsogeny.mapPointsFunctor_app_surjective k
    (TauCeti.AlgHom.mapDomain (q.hom.comp σ) s)
  let P := TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A S S
  let y := P.symm (s, t)
  have hy : y ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup
      (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct S S).obj
      (TauCeti.CommHopfAlgCat.equalizerHopfIdeal (leftToProduct D S q σ) (rightToProduct D S q)) A := by
    rw [points_pullback_iff]
    change TauCeti.AlgHom.mapDomain (q.hom.comp σ) (P y).1 =
      TauCeti.AlgHom.mapDomain q.hom (P y).2
    simp only [y, MulEquiv.apply_symm_apply]
    exact ht.symm
  let z := TauCeti.CommHopfAlgCat.liftQuotientPoint _ _ A y
    ((TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ A y).1 hy)
  refine ⟨z, ?_⟩
  have hz : TauCeti.AlgHom.mapDomain (pullbackQuotientMap D S q σ).hom z = y :=
    TauCeti.CommHopfAlgCat.quotientPointsHom_liftQuotientPoint _ _ A y _
  have hp := congrArg Prod.fst (pullbackPoint_components D S q σ A z)
  rw [hz] at hp
  change (P y).1 = TauCeti.AlgHom.mapDomain (firstProjection D S q σ).hom z at hp
  simp only [y, MulEquiv.apply_symm_apply] at hp
  exact hp.symm

theorem firstProjection_injective [IsAlgClosed k]
    (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (hq : TauCeti.CommHopfAlgCat.IsCentralIsogeny q)
    (σ : D →ₐc[k] D) [IsReduced S] :
    Function.Injective (firstProjection D S q σ).hom := by
  intro a b hab
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro p
  obtain ⟨z, hz⟩ := firstProjection_surjective_points D S q hq σ (toConv p)
  have ha := congrArg (fun f => f.ofConv a) hz
  have hb := congrArg (fun f => f.ofConv b) hz
  rw [TauCeti.AlgHom.mapDomain_apply_apply, hab] at ha
  rw [TauCeti.AlgHom.mapDomain_apply_apply] at hb
  exact ha.symm.trans hb

theorem finite_firstProjection (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (hq : TauCeti.CommHopfAlgCat.IsCentralIsogeny q)
    (σ : D →ₐc[k] D) :
    (firstProjection D S q σ).hom.toAlgHom.Finite := by
  let B := pullbackCoordinate D S q σ
  let l := (firstProjection D S q σ).hom.toAlgHom.toRingHom
  let r := (secondProjection D S q σ).hom.toAlgHom.toRingHom
  have hr : ∀ a : S, l.IsIntegralElem (r a) := by
    intro a
    have hqi : q.hom.toAlgHom.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hq.finite
    have ha := (hqi a).map r
    have heq : r.comp q.hom.toAlgHom.toRingHom =
        l.comp (q.hom.comp σ).toAlgHom.toRingHom := by
      have h := projection_equation D S q σ
      exact congrArg (fun f : D →ₐc[k] B => f.toAlgHom.toRingHom) h.symm
    rw [heq] at ha
    exact ha.of_comp
  have hπ : ∀ v : S ⊗[k] S,
      l.IsIntegralElem ((pullbackQuotientMap D S q σ).hom v) := by
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul a b =>
      have ha := RingHom.isIntegralElem_map l (x := a)
      have hb := hr b
      have h := ha.mul l hb
      have heq : l a * r b = (pullbackQuotientMap D S q σ).hom (a ⊗ₜ[k] b) := by
        change (pullbackQuotientMap D S q σ).hom
          (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft S S) a) *
            (pullbackQuotientMap D S q σ).hom
              (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom (TauCeti.FiniteTypeCommHopfAlgCat.includeRight S S) b) = _
        rw [TauCeti.FiniteTypeCommHopfAlgCat.includeLeft_apply,
          TauCeti.FiniteTypeCommHopfAlgCat.includeRight_apply,
          ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      exact heq ▸ h
    | add v w hv hw =>
      rw [map_add]
      exact hv.add l hw
  have hi : l.IsIntegral := by
    intro b
    obtain ⟨v, rfl⟩ := TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _ b
    exact hπ v
  have hft : l.FiniteType := by
    exact RingHom.FiniteType.of_comp_finiteType (f := algebraMap k S) (g := l)
      ((firstProjection D S q σ).hom.toAlgHom.comp_algebraMap.symm ▸
        RingHom.finiteType_algebraMap.mpr (TauCeti.FiniteTypeCommHopfAlgCat.finiteType B))
  exact hi.to_finite hft

theorem isCentralIsogeny_firstProjection [IsAlgClosed k]
    (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (hq : TauCeti.CommHopfAlgCat.IsCentralIsogeny q)
    (σ : D →ₐc[k] D) [IsReduced S] :
    TauCeti.CommHopfAlgCat.IsCentralIsogeny (firstProjection D S q σ) := by
  have hfin := finite_firstProjection D S q hq σ
  have hdom : DenseRange (PrimeSpectrum.comap (firstProjection D S q σ).hom.toAlgHom.toRingHom) :=
    RingHom.denseRange_comap_of_injective _ (firstProjection_injective D S q hq σ)
  apply (TauCeti.CommHopfAlgCat.isCentralIsogeny_iff _).2
  exact ⟨hfin, TauCeti.CommHopfAlgCat.faithfullyFlat_of_finite_of_dominant _ hfin hdom,
    isCentral_kernel_firstProjection D S q hq σ⟩

end CFSG.LieType.AlgebraicGroups.CentralIsogenyPullback
