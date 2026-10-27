module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentTangent
public import CFSG.LieType.AlgebraicGroups.ToralCentralizerComponent
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LieType.AlgebraicGroups.G2ExceptionalGraph
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Group
public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
public import TauCeti.RingTheory.Idempotents.Connected.Component

public noncomputable section

open CategoryTheory WithConv
open scoped CFSG.ConvolutionPoints

namespace CFSG.LieType.AlgebraicGroups.MatrixComponents

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

attribute [local instance 2000] GrpCat.str

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

noncomputable local instance componentGroupPointsGroup
    (H : TauCeti.FiniteTypeCommHopfAlgCat k) :
    Group ↑(TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints H) :=
  (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints H).str

abbrev coordinateHopf (Z : Subgroup (ModGL τ k)) : TauCeti.FiniteTypeCommHopfAlgCat k :=
  TauCeti.FiniteTypeCommHopfAlgCat.of k
    (GLCoord k (Label τ) ⧸ subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom))

noncomputable local instance componentGroupPointsCoordinateGroup
    (Z : Subgroup (ModGL τ k)) :
    Group ↑(TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints
      (coordinateHopf (τ := τ) (k := k) Z)) :=
  (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints
    (coordinateHopf (τ := τ) (k := k) Z)).str

omit [IsAlgClosed k] in
theorem pointsZero_subgroupIdeal_map_modGLPoint (Z : Subgroup (ModGL τ k))
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k)))) :
    pointsZero k
        (subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom)) =
      subgroupPoints (Z.map (modGLPoint τ k).toMonoidHom) := by
  rw [subgroupIdeal, subgroupPoints_map]
  exact pointsZero_pointsIdeal_of_isPointClosed hZ

@[expose] noncomputable def coordinatePointsMulEquiv (Z : Subgroup (ModGL τ k))
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k)))) :
    @MulEquiv (TauCeti.HopfAlgebra.points (H := coordinateHopf (τ := τ) (k := k) Z)
        (CommAlgCat.of k k)) Z TauCeti.AlgHom.instGroup.toMul _ :=
  let e := mapQuotientPointsEquiv (modGLPoint τ k) Z
    (pointsZero_subgroupIdeal_map_modGLPoint Z hZ)
  { toFun := e.toFun
    invFun := e.invFun
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_mul' := e.map_mul }

theorem coordinatePointsMulEquiv_coe (Z : Subgroup (ModGL τ k))
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))))
    (x : TauCeti.HopfAlgebra.points (H := coordinateHopf Z) (CommAlgCat.of k k)) :
    (coordinatePointsMulEquiv Z hZ x : ModGL τ k) =
      (modGLPoint τ k).symm (toConv (x.ofConv.comp
        (Ideal.Quotient.mkₐ k (subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom))))) := by
  change (mapQuotientPointsEquiv (modGLPoint τ k) Z
    (pointsZero_subgroupIdeal_map_modGLPoint Z hZ) x : ModGL τ k) = _
  exact coe_mapQuotientPointsEquiv (modGLPoint τ k) Z
    (pointsZero_subgroupIdeal_map_modGLPoint Z hZ) x

theorem connectedComponentIn_zeroLocus_subgroupIdeal_closedIdentityComponent
    (Z : Subgroup (ModGL τ k))
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k)))) :
    connectedComponentIn
        (PrimeSpectrum.zeroLocus
          (subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom) : Set (GLCoord k (Label τ))))
        (pointSpec (1 : WithConv (GLCoord k (Label τ) →ₐ[k] k)).ofConv) =
      PrimeSpectrum.zeroLocus
        (subgroupIdeal ((closedIdentityComponent Z).map (modGLPoint τ k).toMonoidHom) :
          Set (GLCoord k (Label τ))) := by
  set E : ModGL τ k ≃* WithConv (GLCoord k (Label τ) →ₐ[k] k) := modGLPoint τ k with hE
  set Zp : Subgroup (WithConv (GLCoord k (Label τ) →ₐ[k] k)) := Z.map E.toMonoidHom with hZp
  set Mp : Subgroup (WithConv (GLCoord k (Label τ) →ₐ[k] k)) :=
    (closedIdentityComponent Z).map E.toMonoidHom with hMp
  have hMZ : Mp ≤ Zp := Subgroup.map_mono (closedIdentityComponent_le Z)
  have hMcl : IsPointClosed k (subgroupPoints Mp) := by
    rw [hMp]
    rw [subgroupPoints_map]
    exact isPointClosed_closedIdentityComponent hZ
  let Hsub : Subgroup Z := (closedIdentityComponent Z).subgroupOf Z
  let r : Z ⧸ Hsub → Z := fun q => q.out
  let rr : Z ⧸ Hsub → WithConv (GLCoord k (Label τ) →ₐ[k] k) := fun q => E.toMonoidHom (r q)
  have hTfin : (Set.range rr).Finite := Set.finite_range rr
  have hTZ : Set.range rr ⊆ (Zp : Set (WithConv (GLCoord k (Label τ) →ₐ[k] k))) := by
    rintro _ ⟨q, rfl⟩
    exact Subgroup.mem_map_of_mem E.toMonoidHom (r q).2
  have hcov : ∀ z ∈ Zp, ∃ t ∈ Set.range rr, t⁻¹ * z ∈ Mp := by
    rintro z ⟨z₀, hz₀, rfl⟩
    let q : Z ⧸ Hsub := QuotientGroup.mk (⟨z₀, hz₀⟩ : Z)
    refine ⟨rr q, ⟨q, rfl⟩, ?_⟩
    have h1 : (QuotientGroup.mk (r q) : Z ⧸ Hsub) = q := QuotientGroup.out_eq' q
    have hmem : ((r q)⁻¹ * (⟨z₀, hz₀⟩ : Z) : Z) ∈ Hsub := QuotientGroup.eq.1 h1
    have h3 : E.toMonoidHom ((r q)⁻¹ * (⟨z₀, hz₀⟩ : Z)) ∈ Mp := by
      rw [hMp]
      exact Subgroup.mem_map_of_mem E.toMonoidHom (Subgroup.mem_subgroupOf.1 hmem)
    simpa only [Subgroup.coe_mul, InvMemClass.coe_inv, map_inv, map_mul] using h3
  have hdiff : IsPointClosed k (subgroupPoints Zp \ subgroupPoints Mp) :=
    isPointClosed_subgroupPoints_diff hMZ hMcl hTfin hTZ hcov
  have hM : IsConnectedAlgebraicSubgroup k Mp := by
    rw [hMp]
    exact isConnectedAlgebraicSubgroup_closedIdentityComponent hZ
  have hcomp := connectedComponentIn_zeroLocus_eq hMZ hM hdiff
  simpa only [hZp, hMp, hE] using hcomp

omit [IsAlgClosed k] in
theorem pointSpec_eq_kernelPoint {A : Type} [CommRing A] [Algebra k A] (y : A →ₐ[k] k) :
    pointSpec y = TauCeti.AlgHom.kernelPoint y := by
  apply PrimeSpectrum.ext
  rw [pointSpec_asIdeal, TauCeti.AlgHom.kernelPoint_asIdeal]
  rfl

theorem kernelPoint_mem_connectedComponent_augmentation_iff
    (Z : Subgroup (ModGL τ k))
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))))
    (φ : WithConv
      ((GLCoord k (Label τ) ⧸ subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom)) →ₐ[k] k)) :
    TauCeti.AlgHom.kernelPoint φ.ofConv ∈
        connectedComponent (TauCeti.Bialgebra.augmentationPoint k
          (GLCoord k (Label τ) ⧸
            subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom))) ↔
      (φ.ofConv.comp
          (Ideal.Quotient.mkₐ k (subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom)))) ∈
        pointsZero k
          (subgroupIdeal ((closedIdentityComponent Z).map (modGLPoint τ k).toMonoidHom)) := by
  let I : Ideal (GLCoord k (Label τ)) :=
    subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom)
  let J : Ideal (GLCoord k (Label τ)) :=
    subgroupIdeal ((closedIdentityComponent Z).map (modGLPoint τ k).toMonoidHom)
  let Aq := GLCoord k (Label τ) ⧸ I
  let e := PrimeSpectrum.quotientHomeomorphZeroLocus I
  let a : PrimeSpectrum Aq :=
    (TauCeti.Bialgebra.augmentationPoint k Aq : PrimeSpectrum Aq)
  let C : Set (PrimeSpectrum Aq) := connectedComponent a
  let x : PrimeSpectrum Aq := TauCeti.AlgHom.kernelPoint φ.ofConv
  have hpt : (e a : PrimeSpectrum (GLCoord k (Label τ))) =
      pointSpec (1 : WithConv (GLCoord k (Label τ) →ₐ[k] k)).ofConv := by
    rw [PrimeSpectrum.quotientHomeomorphZeroLocus_apply_coe]
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal, pointSpec_asIdeal]
    have haker : a.asIdeal = RingHom.ker (Bialgebra.counitAlgHom k Aq : Aq →+* k) := by
      dsimp only [a]
      exact TauCeti.AlgHom.kernelPoint_asIdeal _
    rw [haker]
    change (RingHom.ker (Bialgebra.counitAlgHom k Aq :
        (GLCoord k (Label τ) ⧸ I) →+* k)).comap
      (Ideal.Quotient.mk I :
        GLCoord k (Label τ) →+* (GLCoord k (Label τ) ⧸ I)) =
        RingHom.ker ((1 : WithConv (GLCoord k (Label τ) →ₐ[k] k)).ofConv : _ →+* k)
    rw [RingHom.comap_ker]
    congr 1
  have himg : Subtype.val '' (e '' C) =
      connectedComponentIn (PrimeSpectrum.zeroLocus (I : Set (GLCoord k (Label τ))))
        (pointSpec (1 : WithConv (GLCoord k (Label τ) →ₐ[k] k)).ofConv) := by
    rw [Homeomorph.image_connectedComponent]
    have hsub : e a =
        (⟨pointSpec (1 : WithConv (GLCoord k (Label τ) →ₐ[k] k)).ofConv, by
          rw [PrimeSpectrum.mem_zeroLocus]
          intro b hb
          exact hpt ▸ (e a).2 hb⟩ :
          PrimeSpectrum.zeroLocus (I : Set (GLCoord k (Label τ)))) := by
      exact Subtype.ext hpt
    rw [hsub]
    exact (connectedComponentIn_eq_image
      (show pointSpec (1 : WithConv (GLCoord k (Label τ) →ₐ[k] k)).ofConv ∈
        PrimeSpectrum.zeroLocus (I : Set (GLCoord k (Label τ))) from by
        rw [PrimeSpectrum.mem_zeroLocus]
        intro b hb
        exact hpt ▸ (e a).2 hb)).symm
  have hiff : x ∈ C ↔
      (e x : PrimeSpectrum (GLCoord k (Label τ))) ∈
        connectedComponentIn (PrimeSpectrum.zeroLocus (I : Set (GLCoord k (Label τ))))
          (pointSpec (1 : WithConv (GLCoord k (Label τ) →ₐ[k] k)).ofConv) := by
    rw [← himg]
    constructor
    · intro h
      exact ⟨e _, ⟨_, h, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨y, hy, hxy⟩, hval⟩
      have h1 : y = x := e.injective (hxy.trans (Subtype.ext hval))
      rwa [h1] at hy
  have hex : (e x : PrimeSpectrum (GLCoord k (Label τ))) =
      pointSpec (φ.ofConv.comp (Ideal.Quotient.mkₐ k I)) := by
    rw [PrimeSpectrum.quotientHomeomorphZeroLocus_apply_coe]
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal, pointSpec_asIdeal]
    have hxker : x.asIdeal = RingHom.ker (φ.ofConv : _ →+* k) := by
      dsimp only [x]
      exact TauCeti.AlgHom.kernelPoint_asIdeal _
    rw [hxker]
    change (RingHom.ker (φ.ofConv :
        (GLCoord k (Label τ) ⧸ I) →+* k)).comap
      (Ideal.Quotient.mkₐ k I :
        GLCoord k (Label τ) →+* (GLCoord k (Label τ) ⧸ I)) =
        RingHom.ker ((φ.ofConv : (GLCoord k (Label τ) ⧸ I) →+* k).comp
          (Ideal.Quotient.mkₐ k I :
            GLCoord k (Label τ) →+* (GLCoord k (Label τ) ⧸ I)))
    exact RingHom.comap_ker _ _
  have hcomp := connectedComponentIn_zeroLocus_subgroupIdeal_closedIdentityComponent (τ := τ)
    (k := k) Z hZ
  have hmain : x ∈ C ↔ (φ.ofConv.comp
      (Ideal.Quotient.mkₐ k (subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom)))) ∈
        pointsZero k (subgroupIdeal ((closedIdentityComponent Z).map
          (modGLPoint τ k).toMonoidHom)) := by
    rw [hiff, hex, hcomp, pointSpec_mem_zeroLocus]
  change x ∈ C ↔ (φ.ofConv.comp (Ideal.Quotient.mkₐ k I)) ∈ pointsZero k J
  exact hmain

abbrev identityComponentPointsSubgroup (Z : Subgroup (ModGL τ k)) :
    @Subgroup (TauCeti.HopfAlgebra.points (H := coordinateHopf (τ := τ) (k := k) Z)
      (CommAlgCat.of k k)) TauCeti.AlgHom.instGroup :=
  TauCeti.CommHopfAlgCat.quotientPointsSubgroup (coordinateHopf (τ := τ) (k := k) Z).obj
    (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k)
      (H := coordinateHopf (τ := τ) (k := k) Z))
    (CommAlgCat.of k k)

theorem coordinatePoints_mem_closedIdentityComponent_iff
    (Z : Subgroup (ModGL τ k))
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))))
    (φ : TauCeti.HopfAlgebra.points (H := coordinateHopf (τ := τ) (k := k) Z)
      (CommAlgCat.of k k)) :
    (coordinatePointsMulEquiv Z hZ φ : ModGL τ k) ∈ closedIdentityComponent Z ↔
      φ ∈ identityComponentPointsSubgroup (τ := τ) (k := k) Z := by
  let I : Ideal (GLCoord k (Label τ)) := subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom)
  let J : Ideal (GLCoord k (Label τ)) :=
    subgroupIdeal ((closedIdentityComponent Z).map (modGLPoint τ k).toMonoidHom)
  have hcoe : (coordinatePointsMulEquiv Z hZ φ : ModGL τ k) =
      (modGLPoint τ k).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k I))) := by
    change ((mapQuotientPointsEquiv (modGLPoint τ k) Z
      (pointsZero_subgroupIdeal_map_modGLPoint Z hZ)) φ : ModGL τ k) = _
    exact coe_mapQuotientPointsEquiv (modGLPoint τ k) Z
      (pointsZero_subgroupIdeal_map_modGLPoint Z hZ) φ
  have hmemψ : (φ.ofConv.comp (Ideal.Quotient.mkₐ k I)) ∈ pointsZero k J ↔
      (coordinatePointsMulEquiv Z hZ φ : ModGL τ k) ∈ closedIdentityComponent Z := by
    have hJ : pointsZero k J = subgroupPoints
        ((closedIdentityComponent Z).map (modGLPoint τ k).toMonoidHom) :=
      (isConnectedAlgebraicSubgroup_closedIdentityComponent (τ := τ) (k := k) hZ).pointsZero_eq
    rw [hJ, subgroupPoints_map, mem_transportPoints_modGLPoint, hcoe]
    rfl
  change (coordinatePointsMulEquiv Z hZ φ : ModGL τ k) ∈ closedIdentityComponent Z ↔
    φ ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup (coordinateHopf (τ := τ) (k := k) Z).obj
      (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k)
        (H := coordinateHopf (τ := τ) (k := k) Z))
      (CommAlgCat.of k k)
  rw [TauCeti.FiniteTypeCommHopfAlgCat.mem_identityComponentPointsSubgroup_iff]
  exact ((kernelPoint_mem_connectedComponent_augmentation_iff Z hZ φ).trans hmemψ).symm

theorem map_identityComponentPointsSubgroup_eq
    (Z : Subgroup (ModGL τ k))
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k)))) :
    @Subgroup.map
      (TauCeti.HopfAlgebra.points (H := coordinateHopf (τ := τ) (k := k) Z)
        (CommAlgCat.of k k)) TauCeti.AlgHom.instGroup
      Z (inferInstance) (coordinatePointsMulEquiv Z hZ).toMonoidHom
      (identityComponentPointsSubgroup (τ := τ) (k := k) Z) =
      (closedIdentityComponent Z).subgroupOf Z := by
  ext x
  rw [@Subgroup.mem_map_equiv
    (TauCeti.HopfAlgebra.points (H := coordinateHopf (τ := τ) (k := k) Z)
      (CommAlgCat.of k k)) TauCeti.AlgHom.instGroup
    Z (inferInstance) (coordinatePointsMulEquiv Z hZ)
    (identityComponentPointsSubgroup (τ := τ) (k := k) Z) x,
    Subgroup.mem_subgroupOf]
  simpa only [MulEquiv.apply_symm_apply] using
    (coordinatePoints_mem_closedIdentityComponent_iff Z hZ
      ((coordinatePointsMulEquiv Z hZ).symm x)).symm

noncomputable def componentGroupPointsMulEquivQuotient
    (Z : Subgroup (ModGL τ k))
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k)))) :
    @MulEquiv (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints
        (coordinateHopf (τ := τ) (k := k) Z))
      (Z ⧸ (closedIdentityComponent Z).subgroupOf Z)
      (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints
        (coordinateHopf (τ := τ) (k := k) Z)).str.toMul
      (inferInstance) := by
  let Q : @Subgroup (TauCeti.HopfAlgebra.points
      (H := coordinateHopf (τ := τ) (k := k) Z) (CommAlgCat.of k k))
      TauCeti.AlgHom.instGroup :=
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup
      (coordinateHopf (τ := τ) (k := k) Z).obj
      (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k)
        (H := coordinateHopf (τ := τ) (k := k) Z))
      (CommAlgCat.of k k)
  letI : @Subgroup.Normal (TauCeti.HopfAlgebra.points
      (H := coordinateHopf (τ := τ) (k := k) Z) (CommAlgCat.of k k))
      TauCeti.AlgHom.instGroup Q :=
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup_normal
      (coordinateHopf (τ := τ) (k := k) Z).obj
      (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k)
        (H := coordinateHopf (τ := τ) (k := k) Z))
      (TauCeti.FiniteTypeCommHopfAlgCat.isNormal_identityComponentHopfIdeal
        (coordinateHopf (τ := τ) (k := k) Z))
      (CommAlgCat.of k k)
  have hmap : @Subgroup.map
      (TauCeti.HopfAlgebra.points (H := coordinateHopf (τ := τ) (k := k) Z)
        (CommAlgCat.of k k)) TauCeti.AlgHom.instGroup
      Z (inferInstance) (coordinatePointsMulEquiv Z hZ).toMonoidHom Q =
      (closedIdentityComponent Z).subgroupOf Z := by
    change @Subgroup.map
      (TauCeti.HopfAlgebra.points (H := coordinateHopf (τ := τ) (k := k) Z)
        (CommAlgCat.of k k)) TauCeti.AlgHom.instGroup
      Z (inferInstance) (coordinatePointsMulEquiv Z hZ).toMonoidHom
      (identityComponentPointsSubgroup (τ := τ) (k := k) Z) =
      (closedIdentityComponent Z).subgroupOf Z
    exact map_identityComponentPointsSubgroup_eq Z hZ
  change (TauCeti.HopfAlgebra.points (H := coordinateHopf (τ := τ) (k := k) Z)
      (CommAlgCat.of k k) ⧸ Q) ≃*
    (Z ⧸ (closedIdentityComponent Z).subgroupOf Z)
  exact @QuotientGroup.congr
    (TauCeti.HopfAlgebra.points (H := coordinateHopf (τ := τ) (k := k) Z)
      (CommAlgCat.of k k)) Z TauCeti.AlgHom.instGroup (inferInstance)
    Q ((closedIdentityComponent Z).subgroupOf Z) (inferInstance) (inferInstance)
    (coordinatePointsMulEquiv Z hZ) hmap

theorem isPGroup_componentGroupPoints_iff
    (p : ℕ) (Z : Subgroup (ModGL τ k))
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k)))) :
    IsPGroup p (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints
        (coordinateHopf (τ := τ) (k := k) Z)) ↔
      IsPGroup p (Z ⧸ (closedIdentityComponent Z).subgroupOf Z) := by
  constructor
  · exact fun h => IsPGroup.of_equiv h (componentGroupPointsMulEquivQuotient Z hZ)
  · exact fun h => IsPGroup.of_equiv h (componentGroupPointsMulEquivQuotient Z hZ).symm

end CFSG.LieType.AlgebraicGroups.MatrixComponents
