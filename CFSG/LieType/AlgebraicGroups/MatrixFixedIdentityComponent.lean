module

public import CFSG.LieType.AlgebraicGroups.MatrixFixedComponentsThree
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation

public noncomputable section

open WithConv CategoryTheory
namespace CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

section ConvolutionScoped

open scoped CFSG.ConvolutionPoints

abbrev matrixCentralizerIdeal (M : Subgroup (ModGL τ k)) (a : ModGL τ k) :
    Ideal (GLCoord k (Label τ)) :=
  subgroupIdeal ((M ⊓ Subgroup.centralizer {a}).map (modGLPoint τ k).toMonoidHom)

def matrixFixedBialgHom (M : Subgroup (ModGL τ k)) (a : ModGL τ k)
    (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M) :
    GLCoord k (Label τ) →ₐc[k]
      fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha) :=
  (Bialgebra.Quotient.mkBialgHom (fixedHopfIdeal (MatrixComponents.coordinateHopf M)
    (matrixInnerCoordinate M a ha)).toIdeal).comp
    (Bialgebra.Quotient.mkBialgHom (subgroupIdeal (M.map (modGLPoint τ k).toMonoidHom)))

theorem matrixFixedBialgHom_eq_zero_of_mem (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (ha3 : a ^ 3 = 1) :
    ∀ b ∈ matrixCentralizerIdeal M a, matrixFixedBialgHom M a ha b = 0 := by
  let F := fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)
  let N := M ⊓ Subgroup.centralizer {a}
  let e := modGLPoint τ k
  let : Algebra.Smooth k F := smooth_fixedCoordinate_three (MatrixComponents.coordinateHopf M)
    h3 (matrixInnerCoordinate M a ha) (matrixInnerCoordinate_cube M a ha ha3)
  let : IsReduced F := TauCeti.isReduced_of_smooth k F
  have hf : ∀ z : F →ₐ[k] k, z.comp (matrixFixedBialgHom M a ha).toAlgHom ∈
      transportPoints e (N : Set (ModGL τ k)) := by
    intro z
    refine ⟨matrixFixedPointsHom M hM a ha (toConv z),
      (matrixFixedPointsHom M hM a ha (toConv z)).property, ?_⟩
    change (e (matrixFixedPointsHom M hM a ha (toConv z) : ModGL τ k)).ofConv = _
    dsimp only [e]
    rw [matrixFixedPointsHom_apply, MatrixComponents.coordinatePointsMulEquiv_coe,
      MulEquiv.apply_symm_apply, ofConv_toConv]
    rfl
  intro b hb
  exact map_eq_zero_of_comp_mem (transportPoints e (N : Set (ModGL τ k)))
    (matrixFixedBialgHom M a ha).toAlgHom hf
    (by simpa only [matrixCentralizerIdeal, subgroupIdeal, subgroupPoints_map] using hb)

def matrixFixedCoordinatePointMap (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (ha3 : a ^ 3 = 1) :
    MatrixComponents.coordinateHopf (M ⊓ Subgroup.centralizer {a}) →ₐc[k]
      fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha) :=
  bialgHomQuotientLift (matrixCentralizerIdeal M a) (matrixFixedBialgHom M a ha)
    (matrixFixedBialgHom_eq_zero_of_mem M hM a ha h3 ha3)

theorem matrixFixedCoordinatePointMap_on_points
    (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (ha3 : a ^ 3 = 1)
    (x : TauCeti.HopfAlgebra.points (R := k)
      (H := fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha))
      (CommAlgCat.of k k)) :
    MatrixComponents.coordinatePointsMulEquiv (M ⊓ Subgroup.centralizer {a})
        (isPointClosed_inf hM (isPointClosed_centralizer {a}))
        (TauCeti.AlgHom.mapDomain (matrixFixedCoordinatePointMap M hM a ha h3 ha3) x) =
      matrixFixedPointsHom M hM a ha x := by
  let F := fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)
  let N := M ⊓ Subgroup.centralizer {a}
  let e := modGLPoint τ k
  let I := matrixCentralizerIdeal M a
  let fB := matrixFixedBialgHom M a ha
  let hkill := matrixFixedBialgHom_eq_zero_of_mem M hM a ha h3 ha3
  change MatrixComponents.coordinatePointsMulEquiv N
      (isPointClosed_inf hM (isPointClosed_centralizer {a}))
      (TauCeti.AlgHom.mapDomain (bialgHomQuotientLift I fB hkill) x) = _
  apply Subtype.ext
  rw [MatrixComponents.coordinatePointsMulEquiv_coe, matrixFixedPointsHom_apply,
    MatrixComponents.coordinatePointsMulEquiv_coe]
  apply congrArg e.symm
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro b
  change x.ofConv (bialgHomQuotientLift I fB hkill (Ideal.Quotient.mk I b)) = x.ofConv (fB b)
  rw [bialgHomQuotientLift_mk]

theorem matrixFixedCoordinatePointMap_bijective
    (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (ha3 : a ^ 3 = 1) :
    Function.Bijective (matrixFixedCoordinatePointMap M hM a ha h3 ha3) := by
  let F := fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)
  let N := M ⊓ Subgroup.centralizer {a}
  let hN := isPointClosed_inf hM (isPointClosed_centralizer {a})
  let e := modGLPoint τ k
  let I := matrixCentralizerIdeal M a
  let fB := matrixFixedBialgHom M a ha
  let hkill := matrixFixedBialgHom_eq_zero_of_mem M hM a ha h3 ha3
  let qF : MatrixComponents.coordinateHopf M →ₐc[k] F :=
    Bialgebra.Quotient.mkBialgHom
      (fixedHopfIdeal (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)).toIdeal
  let πb : GLCoord k (Label τ) →ₐc[k] MatrixComponents.coordinateHopf M :=
    Bialgebra.Quotient.mkBialgHom (subgroupIdeal (M.map e.toMonoidHom))
  have hπb : Function.Surjective πb := by
    intro x
    obtain ⟨b, hb⟩ := Ideal.Quotient.mkₐ_surjective k
      (subgroupIdeal (M.map e.toMonoidHom)) x
    exact ⟨b, by simpa only [πb, Bialgebra.Quotient.mkBialgHom_apply,
      Ideal.Quotient.mkₐ_eq_mk] using hb⟩
  have hqF : Function.Surjective qF := by
    intro y
    obtain ⟨c, hc⟩ := Ideal.Quotient.mkₐ_surjective k
      (fixedHopfIdeal (MatrixComponents.coordinateHopf M)
        (matrixInnerCoordinate M a ha)).toIdeal y
    exact ⟨c, by rw [Bialgebra.Quotient.mkBialgHom_apply]; exact hc⟩
  have hfB : Function.Surjective fB := by
    change Function.Surjective (qF.comp πb)
    exact hqF.comp hπb
  refine ⟨?_, ?_⟩
  ·
    have hker : ∀ b, bialgHomQuotientLift I fB hkill b = 0 → b = 0 := by
      intro b hb
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hc0 : fB c = 0 := by
        rwa [bialgHomQuotientLift_mk] at hb
      rw [Ideal.Quotient.eq_zero_iff_mem]
      change c ∈ pointsIdeal (subgroupPoints (N.map e.toMonoidHom))
      rw [mem_pointsIdeal]
      intro y hy
      have hyN : (e.symm (toConv y) : ModGL τ k) ∈ N := (Subgroup.mem_map_equiv).mp hy
      obtain ⟨x, hx⟩ := (matrixFixedPointsHom_bijective M hM a ha).2
        (⟨e.symm (toConv y), hyN⟩ : N)
      have hθ := matrixFixedCoordinatePointMap_on_points M hM a ha h3 ha3 x
      have hx' : matrixFixedPointsHom M hM a ha x = ⟨e.symm (toConv y), hyN⟩ := hx
      let z : TauCeti.HopfAlgebra.points (H := MatrixComponents.coordinateHopf N)
          (CommAlgCat.of k k) :=
        toConv (Ideal.Quotient.liftₐ I y (fun b hb => by
          have h := (mem_subgroupIdeal (H := N.map e.toMonoidHom)).1 hb (toConv y) hy
          simpa only [ofConv_toConv] using h))
      have hz : MatrixComponents.coordinatePointsMulEquiv N hN z = ⟨e.symm (toConv y), hyN⟩ := by
        apply Subtype.ext
        rw [MatrixComponents.coordinatePointsMulEquiv_coe]
        congr 1
      have hzeq : z = TauCeti.AlgHom.mapDomain
          (matrixFixedCoordinatePointMap M hM a ha h3 ha3) x := by
        apply (MatrixComponents.coordinatePointsMulEquiv N hN).injective
        rw [hz, hθ, hx']
      have h1 : z (Ideal.Quotient.mk I c) = y c := rfl
      have h2 : (TauCeti.AlgHom.mapDomain
          (matrixFixedCoordinatePointMap M hM a ha h3 ha3) x)
          (Ideal.Quotient.mk I c) = 0 := by
        rw [TauCeti.AlgHom.mapDomain_apply_apply]
        change x.ofConv (bialgHomQuotientLift I fB hkill (Ideal.Quotient.mk I c)) = 0
        rw [bialgHomQuotientLift_mk, hc0]
        exact map_zero x.ofConv
      rw [← h1, hzeq, h2]
    refine fun b b' hbb => ?_
    have hbb' : bialgHomQuotientLift I fB hkill b =
        bialgHomQuotientLift I fB hkill b' := hbb
    have h : b - b' = 0 := hker (b - b') (by rw [map_sub, hbb', sub_self])
    exact sub_eq_zero.mp h
  ·
    intro y
    obtain ⟨b, rfl⟩ := hfB y
    exact ⟨Ideal.Quotient.mk I b, bialgHomQuotientLift_mk I fB hkill b⟩

def coordinateHopfCentralizerIsoFixedCoordinate
    (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (ha3 : a ^ 3 = 1) :
    MatrixComponents.coordinateHopf (M ⊓ Subgroup.centralizer {a}) ≅
      fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha) :=
  CategoryTheory.ObjectProperty.isoMk (TauCeti.finiteTypeCommHopfAlgProperty k)
    (_root_.CommHopfAlgCat.isoMk
    (BialgEquiv.ofBijective (matrixFixedCoordinatePointMap M hM a ha h3 ha3)
      (matrixFixedCoordinatePointMap_bijective M hM a ha h3 ha3)))

theorem smooth_coordinateHopf_centralizer
    (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (ha3 : a ^ 3 = 1) :
    Algebra.Smooth k (MatrixComponents.coordinateHopf (M ⊓ Subgroup.centralizer {a})) := by
  let : Algebra.Smooth k
      (fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)) :=
    smooth_fixedCoordinate_three (MatrixComponents.coordinateHopf M) h3
      (matrixInnerCoordinate M a ha) (matrixInnerCoordinate_cube M a ha ha3)
  exact Algebra.Smooth.of_equiv
    (BialgEquiv.ofBijective (matrixFixedCoordinatePointMap M hM a ha h3 ha3)
      (matrixFixedCoordinatePointMap_bijective M hM a ha h3 ha3)).symm.toAlgEquiv

theorem map_connectedComponentIdempotent_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [LocallyConnectedSpace (PrimeSpectrum R)] [LocallyConnectedSpace (PrimeSpectrum S)]
    (e : R ≃+* S) (x : PrimeSpectrum R) :
    e (PrimeSpectrum.connectedComponentIdempotent x) =
      PrimeSpectrum.connectedComponentIdempotent (PrimeSpectrum.comap (e.symm : S →+* R) x) := by
  let h : PrimeSpectrum R ≃ₜ PrimeSpectrum S := PrimeSpectrum.homeomorphOfRingEquiv e
  have h_apply (y : PrimeSpectrum R) : h y = PrimeSpectrum.comap (e.symm : S →+* R) y := rfl
  have hpre : h ⁻¹' (PrimeSpectrum.basicOpen (e (PrimeSpectrum.connectedComponentIdempotent x)) :
      Set (PrimeSpectrum S)) =
      (PrimeSpectrum.basicOpen (PrimeSpectrum.connectedComponentIdempotent x) :
        Set (PrimeSpectrum R)) := by
    rw [show (h : PrimeSpectrum R → PrimeSpectrum S) =
      PrimeSpectrum.comap (e.symm : S →+* R) from funext h_apply]
    simp
  have himage : h '' (PrimeSpectrum.basicOpen (PrimeSpectrum.connectedComponentIdempotent x) :
      Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen (e (PrimeSpectrum.connectedComponentIdempotent x)) :
        Set (PrimeSpectrum S)) := by
    rw [← hpre]
    exact Set.image_preimage_eq _ h.surjective
  have hcomp : h '' (connectedComponent x : Set (PrimeSpectrum R)) =
      connectedComponent (h x) := by
    simpa only [Set.image_univ, h.surjective.range_eq, connectedComponentIn_univ] using
      h.image_connectedComponentIn (s := Set.univ) (x := x) (Set.mem_univ x)
  apply (PrimeSpectrum.eq_connectedComponentIdempotent_iff
    ((PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent x).map e.toRingHom)
    (PrimeSpectrum.comap (e.symm : S →+* R) x)).mpr
  calc
    (PrimeSpectrum.basicOpen (e (PrimeSpectrum.connectedComponentIdempotent x)) :
        Set (PrimeSpectrum S)) =
        h '' (PrimeSpectrum.basicOpen (PrimeSpectrum.connectedComponentIdempotent x) :
          Set (PrimeSpectrum R)) := himage.symm
    _ = h '' (connectedComponent x : Set (PrimeSpectrum R)) := by
      rw [PrimeSpectrum.basicOpen_connectedComponentIdempotent]
    _ = connectedComponent (h x) := hcomp
    _ = connectedComponent
        (PrimeSpectrum.comap (e.symm : S →+* R) x) := by rw [h_apply]

theorem map_connectedComponentIdeal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [LocallyConnectedSpace (PrimeSpectrum R)] [LocallyConnectedSpace (PrimeSpectrum S)]
    (e : R ≃+* S) (x : PrimeSpectrum R) :
    Ideal.map e (PrimeSpectrum.connectedComponentIdeal x) =
      PrimeSpectrum.connectedComponentIdeal (PrimeSpectrum.comap (e.symm : S →+* R) x) := by
  ext r
  rw [Ideal.mem_map_of_equiv e r]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [PrimeSpectrum.mem_connectedComponentIdeal_iff] at ha ⊢
    obtain ⟨c, hc⟩ := ha
    refine ⟨e c, ?_⟩
    rw [← hc, map_mul, map_sub, map_one, map_connectedComponentIdempotent_of_ringEquiv]
  · intro hr
    rw [PrimeSpectrum.mem_connectedComponentIdeal_iff] at hr
    obtain ⟨b, hb⟩ := hr
    refine ⟨e.symm b * (1 - PrimeSpectrum.connectedComponentIdempotent x), ?_, ?_⟩
    · rw [PrimeSpectrum.mem_connectedComponentIdeal_iff]
      exact ⟨e.symm b, rfl⟩
    · rw [map_mul, map_sub, map_one, map_connectedComponentIdempotent_of_ringEquiv,
        e.apply_symm_apply, hb]

theorem comapOfSurjective_identityComponentHopfIdeal_eq
    {X Y : TauCeti.FiniteTypeCommHopfAlgCat.{0, 0} k} (e : X ≅ Y) :
    (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := Y)).comapOfSurjective
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (CategoryTheory.ConcreteCategory.bijective_of_isIso e.hom).2 =
      TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := X) := by
  let f := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.hom
  let g := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.inv
  have hgf : g.comp f = BialgHom.id k X := by
    rw [← TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_comp, e.hom_inv_id,
      TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_id]
  have hfg : f.comp g = BialgHom.id k Y := by
    rw [← TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_comp, e.inv_hom_id,
      TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_id]
  have hg : Function.Bijective g := CategoryTheory.ConcreteCategory.bijective_of_isIso e.inv
  let gae : Y ≃ₐ[k] X := BialgEquiv.ofBijective g hg
  let ge : Y ≃+* X := gae.toRingEquiv
  have hge_symm : (ge.symm : X →+* Y) = (f : X →+* Y) := by
    ext x
    change gae.symm x = f x
    apply hg.1
    change gae (gae.symm x) = gae (f x)
    rw [gae.apply_symm_apply]
    exact (congrArg (fun φ : X →ₐc[k] X => φ x) hgf).symm
  have hIY : (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := Y)).toIdeal =
      PrimeSpectrum.connectedComponentIdeal
        (pointSpec (Bialgebra.counitAlgHom k Y)) := by
    rw [TauCeti.HopfAlgebra.identityComponentHopfIdeal_toIdeal,
      TauCeti.Bialgebra.augmentationPoint]
    exact congrArg PrimeSpectrum.connectedComponentIdeal
      (MatrixComponents.pointSpec_eq_kernelPoint (Bialgebra.counitAlgHom k Y)).symm
  have hIX : (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := X)).toIdeal =
      PrimeSpectrum.connectedComponentIdeal
        (pointSpec (Bialgebra.counitAlgHom k X)) := by
    rw [TauCeti.HopfAlgebra.identityComponentHopfIdeal_toIdeal,
      TauCeti.Bialgebra.augmentationPoint]
    exact congrArg PrimeSpectrum.connectedComponentIdeal
      (MatrixComponents.pointSpec_eq_kernelPoint (Bialgebra.counitAlgHom k X)).symm
  have hcomap_aug : PrimeSpectrum.comap (f : X →+* Y)
      (pointSpec (Bialgebra.counitAlgHom k Y)) =
      pointSpec (Bialgebra.counitAlgHom k X) := by
    have h := comap_pointSpec (k := k) (A := Y) (B := X) (f : X →ₐ[k] Y)
      (Bialgebra.counitAlgHom k Y)
    rw [show (Bialgebra.counitAlgHom k Y).comp (f : X →ₐ[k] Y) =
      Bialgebra.counitAlgHom k X from BialgHom.counitAlgHom_comp f] at h
    exact h
  have hcomap_map : Ideal.comap (f : X →+* Y)
      (PrimeSpectrum.connectedComponentIdeal (pointSpec (Bialgebra.counitAlgHom k Y))) =
      Ideal.map ge
        (PrimeSpectrum.connectedComponentIdeal
          (pointSpec (Bialgebra.counitAlgHom k Y))) := by
    ext z
    rw [Ideal.mem_comap, Ideal.mem_map_of_equiv ge z]
    constructor
    · intro hz
      exact ⟨f z, hz, congrArg (fun φ : X →ₐc[k] X => φ z) hgf⟩
    · rintro ⟨y, hy, rfl⟩
      show f (g y) ∈ _
      rw [show f (g y) = y from congrArg (fun φ : Y →ₐc[k] Y => φ y) hfg]
      exact hy
  apply TauCeti.HopfIdeal.ext
  intro x
  rw [← TauCeti.HopfIdeal.mem_toIdeal, ← TauCeti.HopfIdeal.mem_toIdeal,
    TauCeti.HopfIdeal.comapOfSurjective_toIdeal, hIY, hcomap_map,
    map_connectedComponentIdeal_of_ringEquiv ge (pointSpec (Bialgebra.counitAlgHom k Y)),
    hge_symm, hcomap_aug, hIX]

def identityComponentIsoOfIso {X Y : TauCeti.FiniteTypeCommHopfAlgCat.{0, 0} k} (e : X ≅ Y) :
    TauCeti.FiniteTypeCommHopfAlgCat.identityComponent X ≅
      TauCeti.FiniteTypeCommHopfAlgCat.identityComponent Y :=
  (CategoryTheory.eqToIso (congrArg (TauCeti.FiniteTypeCommHopfAlgCat.quotient X)
    (comapOfSurjective_identityComponentHopfIdeal_eq e))).symm ≪≫
    TauCeti.FiniteTypeCommHopfAlgCat.quotientIsoOfIso e
      (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := Y))

def identityComponentCoordinateHopfIsoClosedIdentityComponent
    (Z : Subgroup (ModGL τ k))
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))))
    [Algebra.Smooth k (MatrixComponents.coordinateHopf Z)] :
    TauCeti.FiniteTypeCommHopfAlgCat.identityComponent (MatrixComponents.coordinateHopf Z) ≅
      MatrixComponents.coordinateHopf (closedIdentityComponent Z) := by
  let H := MatrixComponents.coordinateHopf Z
  let Hz := H.obj
  let Zc := closedIdentityComponent Z
  let hZc := isPointClosed_closedIdentityComponent hZ
  let e := modGLPoint τ k
  let I : Ideal (GLCoord k (Label τ)) := subgroupIdeal (Z.map e.toMonoidHom)
  let Ic : Ideal (GLCoord k (Label τ)) := subgroupIdeal (Zc.map e.toMonoidHom)
  let I_id : TauCeti.HopfIdeal k Hz :=
    TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)
  have hle : I ≤ Ic := by
    intro b hb
    change b ∈ pointsIdeal (subgroupPoints (Z.map e.toMonoidHom)) at hb
    change b ∈ pointsIdeal (subgroupPoints (Zc.map e.toMonoidHom))
    rw [mem_pointsIdeal] at hb ⊢
    intro y hy
    exact hb y (Subgroup.map_mono (closedIdentityComponent_le Z) hy)
  let q0 : GLCoord k (Label τ) →ₐc[k] (MatrixComponents.coordinateHopf Zc).obj :=
    Bialgebra.Quotient.mkBialgHom (R := k) Ic
  have hq0eq : (q0 : GLCoord k (Label τ) →ₐ[k] (MatrixComponents.coordinateHopf Zc).obj) =
      Ideal.Quotient.mkₐ k Ic :=
    Bialgebra.Quotient.mkBialgHom_toAlgHom (J := Ic)
  have hkill : ∀ b ∈ I, q0 b = 0 := by
    intro b hb
    have hq0 : q0 b = Ideal.Quotient.mk Ic b := by
      simpa only [Ideal.Quotient.mkₐ_eq_mk, BialgHom.coe_toAlgHom] using
        congrArg (fun φ : GLCoord k (Label τ) →ₐ[k]
          (MatrixComponents.coordinateHopf Zc).obj => φ b) hq0eq
    rw [hq0, Ideal.Quotient.eq_zero_iff_mem]
    exact hle hb
  let q : Hz →ₐc[k] (MatrixComponents.coordinateHopf Zc).obj :=
    bialgHomQuotientLift I q0 hkill
  have hq : Function.Surjective q := by
    intro y
    have hy : ∃ b, q0 b = y := by
      obtain ⟨b, hb⟩ := Ideal.Quotient.mkₐ_surjective k Ic y
      exact ⟨b, by
        rw [show q0 b = Ideal.Quotient.mkₐ k Ic b from by
          simpa only [BialgHom.coe_toAlgHom] using
            congrArg (fun φ : GLCoord k (Label τ) →ₐ[k]
              (MatrixComponents.coordinateHopf Zc).obj => φ b) hq0eq]
        exact hb⟩
    obtain ⟨b, rfl⟩ := hy
    exact ⟨Ideal.Quotient.mk I b, bialgHomQuotientLift_mk I q0 hkill b⟩
  let J : TauCeti.HopfIdeal k Hz := TauCeti.HopfIdeal.kerOfSurjective q hq
  have hq_comp : (q : Hz →ₐ[k] (MatrixComponents.coordinateHopf Zc).obj).comp
      (Ideal.Quotient.mkₐ k I) =
      (q0 : GLCoord k (Label τ) →ₐ[k] (MatrixComponents.coordinateHopf Zc).obj) := by
    ext b
    change bialgHomQuotientLift I q0 hkill (Ideal.Quotient.mk I b) = q0 b
    exact bialgHomQuotientLift_mk I q0 hkill b
  let A := CommAlgCat.of k k
  let φZ := MatrixComponents.coordinatePointsMulEquiv Z hZ
  let φZc := MatrixComponents.coordinatePointsMulEquiv Zc hZc
  have hkey : ∀ g'' : TauCeti.HopfAlgebra.points
      (H := (MatrixComponents.coordinateHopf Zc).obj) A,
      ((φZ (TauCeti.AlgHom.mapDomain q g'')) : ModGL τ k) = (φZc g'' : ModGL τ k) := by
    intro g''
    rw [MatrixComponents.coordinatePointsMulEquiv_coe,
      MatrixComponents.coordinatePointsMulEquiv_coe]
    have h1 : (TauCeti.AlgHom.mapDomain q g'').ofConv.comp (Ideal.Quotient.mkₐ k I) =
        g''.ofConv.comp (Ideal.Quotient.mkₐ k Ic) := by
      rw [TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_assoc, hq_comp, hq0eq]
    exact congrArg (fun x => e.symm (WithConv.toConv x)) h1
  have hfactor : ∀ g : TauCeti.HopfAlgebra.points (H := Hz) A,
      (∀ b, q b = 0 → g.ofConv b = 0) →
      ∃ g'' : TauCeti.HopfAlgebra.points (H := (MatrixComponents.coordinateHopf Zc).obj) A,
        TauCeti.AlgHom.mapDomain q g'' = g := by
    intro g hg
    let f : Hz →ₐ[k] A := g.ofConv
    have hf : ∀ x ∈ RingHom.ker (q : Hz →ₐ[k]
        (MatrixComponents.coordinateHopf Zc).obj), f x = 0 := hg
    let g'' : TauCeti.HopfAlgebra.points (H := (MatrixComponents.coordinateHopf Zc).obj) A :=
      toConv ((Ideal.Quotient.liftₐ (RingHom.ker (q : Hz →ₐ[k]
        (MatrixComponents.coordinateHopf Zc).obj)) f hf).comp
          (Ideal.quotientKerAlgEquivOfSurjective (f := (q : Hz →ₐ[k]
            (MatrixComponents.coordinateHopf Zc).obj)) hq).symm.toAlgHom)
    refine ⟨g'', ?_⟩
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    change ((Ideal.Quotient.liftₐ (RingHom.ker (q : Hz →ₐ[k]
        (MatrixComponents.coordinateHopf Zc).obj)) f hf).comp
      (Ideal.quotientKerAlgEquivOfSurjective (f := (q : Hz →ₐ[k]
        (MatrixComponents.coordinateHopf Zc).obj)) hq).symm.toAlgHom) (q b) = f b
    rw [AlgHom.comp_apply]
    change (Ideal.Quotient.liftₐ (RingHom.ker (q : Hz →ₐ[k]
        (MatrixComponents.coordinateHopf Zc).obj)) f hf)
      ((Ideal.quotientKerAlgEquivOfSurjective (f := (q : Hz →ₐ[k]
        (MatrixComponents.coordinateHopf Zc).obj)) hq).symm (q b)) = f b
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective (f := (q : Hz →ₐ[k]
        (MatrixComponents.coordinateHopf Zc).obj)) hq).symm (q b) =
        Ideal.Quotient.mk (RingHom.ker (q : Hz →ₐ[k]
          (MatrixComponents.coordinateHopf Zc).obj)) b := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk (f := (q : Hz →ₐ[k]
        (MatrixComponents.coordinateHopf Zc).obj)) hq b).symm
    rw [h1]
    rfl
  have hImem : ∀ g : TauCeti.HopfAlgebra.points (H := Hz) A,
      g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup Hz I_id A ↔
      (φZ g : ModGL τ k) ∈ Zc := by
    intro g
    exact (MatrixComponents.coordinatePoints_mem_closedIdentityComponent_iff Z hZ g).symm
  have hJmem : ∀ g : TauCeti.HopfAlgebra.points (H := Hz) A,
      g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup Hz J A ↔
      (φZ g : ModGL τ k) ∈ Zc := by
    intro g
    constructor
    · intro hg
      have hker : ∀ b, q b = 0 → g.ofConv b = 0 := by
        intro b hb
        exact (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff Hz J A g).mp hg b
          (by rwa [TauCeti.HopfIdeal.mem_kerOfSurjective])
      obtain ⟨g'', hg''⟩ := hfactor g hker
      rw [show (φZ g : ModGL τ k) = (φZc g'' : ModGL τ k) from by rw [← hg'', hkey]]
      exact (φZc g'').property
    · intro hx
      let g'' : TauCeti.HopfAlgebra.points (H := (MatrixComponents.coordinateHopf Zc).obj) A :=
        φZc.symm ⟨(φZ g : ModGL τ k), hx⟩
      have hval : TauCeti.AlgHom.mapDomain q g'' = g := by
        apply φZ.injective
        apply Subtype.ext
        rw [hkey]
        exact congrArg Subtype.val (φZc.apply_symm_apply ⟨(φZ g : ModGL τ k), hx⟩)
      rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
      intro b hb
      rw [show g = TauCeti.AlgHom.mapDomain q g'' from hval.symm,
        TauCeti.AlgHom.mapDomain_apply_apply]
      rw [show q b = 0 from by rwa [TauCeti.HopfIdeal.mem_kerOfSurjective] at hb]
      exact map_zero g''.ofConv
  have hpoints : TauCeti.CommHopfAlgCat.quotientPointsSubgroup Hz I_id A =
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup Hz J A :=
    @Subgroup.ext (TauCeti.HopfAlgebra.points (H := Hz) A) TauCeti.AlgHom.instGroup
      (TauCeti.CommHopfAlgCat.quotientPointsSubgroup Hz I_id A)
      (TauCeti.CommHopfAlgCat.quotientPointsSubgroup Hz J A)
      (fun g => (hImem g).trans (hJmem g).symm)
  have hredI : IsReduced (TauCeti.CommHopfAlgCat.quotient Hz I_id) := by
    have : Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent H) :=
      TauCeti.FiniteTypeCommHopfAlgCat.smooth_identityComponent H
    exact TauCeti.isReduced_of_smooth k _
  have hredJ : IsReduced (TauCeti.CommHopfAlgCat.quotient Hz J) := by
    have : IsReduced (MatrixComponents.coordinateHopf Zc).obj := by
      change IsReduced (GLCoord k (Label τ) ⧸ subgroupIdeal (Zc.map e.toMonoidHom))
      exact (Ideal.isRadical_iff_quotient_reduced _).1 (isRadical_pointsIdeal _)
    exact TauCeti.HopfIdeal.isReduced_quotient_kerOfSurjective q hq
  have hJ : J = I_id := by
    symm
    exact TauCeti.HopfIdeal.eq_of_quotientPointsSubgroup_eq (H := Hz)
      (I := I_id) (J := J) (K := k) hpoints
  let eJ : TauCeti.CommHopfAlgCat.quotient Hz J ≅
      (MatrixComponents.coordinateHopf Zc).obj :=
    TauCeti.CommHopfAlgCat.quotientIsoOfKerOfSurjectiveEq
      (_root_.CommHopfAlgCat.ofHom q) hq rfl
  exact (CategoryTheory.eqToIso (congrArg
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient H) hJ)).symm ≪≫
    CategoryTheory.ObjectProperty.isoMk (TauCeti.finiteTypeCommHopfAlgProperty k) eJ

theorem reductive_coordinate_closedIdentityComponent_centralizer_of_fixedCoordinate
    (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M) (ha3 : a ^ 3 = 1)
    (hF : TauCeti.reductiveCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent
        (fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)))) :
    TauCeti.reductiveCommHopfAlgProperty k
      (MatrixComponents.coordinateHopf
        (closedIdentityComponent (M ⊓ Subgroup.centralizer {a}))) := by
  let N := M ⊓ Subgroup.centralizer {a}
  have hN : IsPointClosed k (transportPoints (modGLPoint τ k) (N : Set (ModGL τ k))) :=
    isPointClosed_inf hM (isPointClosed_centralizer {a})
  have : Algebra.Smooth k (MatrixComponents.coordinateHopf N) :=
    smooth_coordinateHopf_centralizer M hM a ha h3 ha3
  have hIso : TauCeti.FiniteTypeCommHopfAlgCat.identityComponent
        (fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)) ≅
      MatrixComponents.coordinateHopf (closedIdentityComponent N) :=
    (identityComponentIsoOfIso
      (coordinateHopfCentralizerIsoFixedCoordinate M hM a ha h3 ha3)).symm ≪≫
      identityComponentCoordinateHopfIsoClosedIdentityComponent N hN
  exact (TauCeti.reductiveCommHopfAlgProperty k).prop_of_iso hIso hF

end ConvolutionScoped

end CFSG.LieType.AlgebraicGroups
