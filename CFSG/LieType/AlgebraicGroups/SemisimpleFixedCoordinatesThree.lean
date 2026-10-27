module

public import CFSG.LieType.AlgebraicGroups.FixedPermutationTorus
public import CFSG.LieType.AlgebraicGroups.PermutationTorusAutomorphism
public import CFSG.LieType.AlgebraicGroups.FixedUnipotentConnected
public import CFSG.LieType.AlgebraicGroups.FixedCoordinateEmbedding
public import CFSG.LieType.AlgebraicGroups.FixedBruhatFactorization
public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Semisimple
public import CFSG.LieType.AlgebraicGroups.FixedComponentSmooth
import CFSG.Mathlib.RingTheory.ConnectedRegular

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

abbrev RationalGroup (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :=
  WithConv (H.obj →ₐ[k] k)

abbrev WeightTorus (k : Type u) [Field k] (r : ℕ) :=
  TauCeti.FiniteTypeCommHopfAlgCat.of k
    (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))

abbrev coordinateImage {H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (f : H →ₐc[k] K) : Subgroup (RationalGroup H) :=
  (TauCeti.AlgHom.mapDomain (A := k) f).range

omit [IsAlgClosed k] in
theorem disjoint_of_semisimplePoints_of_unipotentPoints
    {H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    {T U : Subgroup (RationalGroup H)}
    (hT : ∀ x ∈ T, TauCeti.HopfAlgebra.IsSemisimplePoint x)
    (hU : ∀ x ∈ U, TauCeti.HopfAlgebra.IsUnipotentPoint x) : Disjoint T U := by
  apply Subgroup.disjoint_def.mpr
  intro x hxT hxU
  apply TauCeti.Tannaka.fgPoint_ext_of_forall_ofLinearEquiv_pointsAction k H k
  intro M
  let V := TensorProduct k k M
  let g : LinearMap.GeneralLinearGroup k V :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv (TauCeti.Comodule.pointsAction M x)
  let f : Module.End k V := g
  have hss : LinearMap.GeneralLinearGroup.IsSemisimple g :=
    (TauCeti.HopfAlgebra.isSemisimplePoint_def x).mp (hT x hxT) M
  have hs : f.IsSemisimple := (LinearMap.GeneralLinearGroup.isSemisimple_def g).mp hss
  have huu : LinearMap.GeneralLinearGroup.IsUnipotent g :=
    (TauCeti.HopfAlgebra.isUnipotentPoint_def x).mp (hU x hxU) M
  have hu : IsNilpotent (f - 1) := (LinearMap.GeneralLinearGroup.isUnipotent_def g).mp huu
  have hs' : (f - 1).IsSemisimple := by
    simpa only [map_one] using
      (Module.End.isSemisimple_sub_algebraMap_iff (f := f) (μ := (1 : k))).mpr hs
  have hg : g = 1 := Units.ext
    (sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hu hs'))
  have hOne : LinearMap.GeneralLinearGroup.ofLinearEquiv (1 : V ≃ₗ[k] V) = 1 := by
    have h := LinearMap.GeneralLinearGroup.ofLinearEquiv_mul (1 : V ≃ₗ[k] V) 1
    simpa only [one_mul, mul_eq_left] using h.symm
  simpa only [g, map_one, hOne] using hg

omit [IsAlgClosed k] in
theorem coordinateImage_stable_of_equivariant
    (H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σ : H →ₐc[k] H) (τ : K →ₐc[k] K) (f : H →ₐc[k] K)
    (hf : f.comp σ = τ.comp f) :
    ∀ x ∈ coordinateImage f, TauCeti.AlgHom.mapDomain σ x ∈ coordinateImage f := by
  rintro _ ⟨x, rfl⟩
  refine ⟨TauCeti.AlgHom.mapDomain τ x, ?_⟩
  rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp,
    ← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, hf]

structure StableTriangularCoordinates
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : H →ₐc[k] H) where
  rank : ℕ
  torusMap : H →ₐc[k] WeightTorus k rank
  torusSurjective : Function.Surjective torusMap
  torusMaximal : TauCeti.HopfIdeal.IsMaximalTorus k H.obj
    (TauCeti.HopfIdeal.kerOfSurjective torusMap torusSurjective)
  torusAut : WeightTorus k rank →ₐc[k] WeightTorus k rank
  torusEquivariant : torusMap.comp σ = torusAut.comp torusMap
  weightPerm : Equiv.Perm (ULift.{u} (Fin rank))
  torusOnWeight : ∀ i : ULift.{u} (Fin rank),
    torusAut (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
      MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (weightPerm i) 1)) 1
  positive : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k
  negative : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k
  positiveMap : H.obj ⟶ positive.obj
  negativeMap : H.obj ⟶ negative.obj
  positiveSurjective : Function.Surjective positiveMap.hom
  negativeSurjective : Function.Surjective negativeMap.hom
  positiveSmooth : Algebra.Smooth k positive
  negativeSmooth : Algebra.Smooth k negative
  positiveConnected : TauCeti.geometricallyConnectedCommHopfAlgProperty k positive.obj
  negativeConnected : TauCeti.geometricallyConnectedCommHopfAlgProperty k negative.obj
  positiveUnipotentPoints : ∀ x : RationalGroup positive, TauCeti.HopfAlgebra.IsUnipotentPoint x
  negativeUnipotentPoints : ∀ x : RationalGroup negative, TauCeti.HopfAlgebra.IsUnipotentPoint x
  positiveAut : positive →ₐc[k] positive
  negativeAut : negative →ₐc[k] negative
  positiveEquivariant : positiveMap.hom.comp σ = positiveAut.comp positiveMap.hom
  negativeEquivariant : negativeMap.hom.comp σ = negativeAut.comp negativeMap.hom
  positiveBorel : TauCeti.HopfIdeal k H
  negativeBorel : TauCeti.HopfIdeal k H
  isPositiveBorel : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H positiveBorel
  isNegativeBorel : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H negativeBorel
  positiveBorelPoints : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj positiveBorel
      (CommAlgCat.of k k) =
    coordinateImage torusMap ⊔
      coordinateImage positiveMap.hom
  negativeBorelPoints : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj negativeBorel
      (CommAlgCat.of k k) =
    coordinateImage torusMap ⊔
      coordinateImage negativeMap.hom
  torusNormalizesPositive : coordinateImage torusMap ≤
    Subgroup.normalizer (coordinateImage positiveMap.hom : Set (RationalGroup H))
  torusNormalizesNegative : coordinateImage torusMap ≤
    Subgroup.normalizer (coordinateImage negativeMap.hom : Set (RationalGroup H))
  opposite : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj positiveBorel
      (CommAlgCat.of k k) ⊓ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj negativeBorel
      (CommAlgCat.of k k) = coordinateImage torusMap
  inversion : RationalGroup H → Set (RationalGroup H)
  inversionPositive : ∀ n, inversion n ⊆ (coordinateImage positiveMap.hom : Set (RationalGroup H))
  inversionStable : ∀ n ∈ Subgroup.normalizer
      (coordinateImage torusMap : Set (RationalGroup H)),
    ∀ v ∈ inversion n, TauCeti.AlgHom.mapDomain σ v ∈
      inversion (TauCeti.AlgHom.mapDomain σ n)
  bruhatCover : ∀ g : RationalGroup H,
    ∃ u ∈ coordinateImage positiveMap.hom,
    ∃ n ∈ Subgroup.normalizer
      (coordinateImage torusMap : Set (RationalGroup H)),
    ∃ v ∈ inversion n, g = u * n * v
  bruhatUnique : ∀ u ∈ coordinateImage positiveMap.hom,
    ∀ n ∈ Subgroup.normalizer
      (coordinateImage torusMap : Set (RationalGroup H)),
    ∀ v ∈ inversion n,
    ∀ u' ∈ coordinateImage positiveMap.hom,
    ∀ n' ∈ Subgroup.normalizer
      (coordinateImage torusMap : Set (RationalGroup H)),
    ∀ v' ∈ inversion n', u * n * v = u' * n' * v' → u = u' ∧ n = n' ∧ v = v'

namespace StableTriangularCoordinates

variable {H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} {σ : H →ₐc[k] H}
variable (D : StableTriangularCoordinates H σ)

abbrev torus : Subgroup (RationalGroup H) :=
  coordinateImage D.torusMap

abbrev positiveGroup : Subgroup (RationalGroup H) :=
  coordinateImage D.positiveMap.hom

abbrev negativeGroup : Subgroup (RationalGroup H) :=
  coordinateImage D.negativeMap.hom

abbrev normalizer : Subgroup (RationalGroup H) := Subgroup.normalizer (D.torus : Set _)

abbrev fixed (_D : StableTriangularCoordinates H σ) : Subgroup (RationalGroup H) :=
  TauCeti.fixedSubgroup (TauCeti.AlgHom.mapDomain σ)

abbrev connectedGenerators : Subgroup (RationalGroup H) :=
  (D.torus ⊓ D.fixed) ⊔ (D.positiveGroup ⊓ D.fixed) ⊔ (D.negativeGroup ⊓ D.fixed)

omit [IsAlgClosed k] in
theorem positiveUnipotent (x : RationalGroup D.positive) :
    TauCeti.HopfAlgebra.IsUnipotentPoint (TauCeti.AlgHom.mapDomain D.positiveMap.hom x) :=
  (D.positiveUnipotentPoints x).mapDomain D.positiveMap.hom

omit [IsAlgClosed k] in
theorem negativeUnipotent (x : RationalGroup D.negative) :
    TauCeti.HopfAlgebra.IsUnipotentPoint (TauCeti.AlgHom.mapDomain D.negativeMap.hom x) :=
  (D.negativeUnipotentPoints x).mapDomain D.negativeMap.hom

omit [IsAlgClosed k] in
theorem torus_points_semisimple :
    ∀ x ∈ D.torus, TauCeti.HopfAlgebra.IsSemisimplePoint x := by
  rintro _ ⟨t, rfl⟩
  exact (TauCeti.DiagonalizableGroup.isSemisimplePoint t).mapDomain D.torusMap

omit [IsAlgClosed k] in
theorem torusDisjointPositive :
    Disjoint (coordinateImage D.torusMap) (coordinateImage D.positiveMap.hom) := by
  apply disjoint_of_semisimplePoints_of_unipotentPoints D.torus_points_semisimple
  rintro _ ⟨u, rfl⟩
  exact D.positiveUnipotent u

omit [IsAlgClosed k] in
theorem torusDisjointNegative :
    Disjoint (coordinateImage D.torusMap) (coordinateImage D.negativeMap.hom) := by
  apply disjoint_of_semisimplePoints_of_unipotentPoints D.torus_points_semisimple
  rintro _ ⟨u, rfl⟩
  exact D.negativeUnipotent u

omit [IsAlgClosed k] in
theorem positiveStable : ∀ x ∈ coordinateImage D.positiveMap.hom,
    TauCeti.AlgHom.mapDomain σ x ∈ coordinateImage D.positiveMap.hom :=
  coordinateImage_stable_of_equivariant H D.positive σ D.positiveAut
    D.positiveMap.hom D.positiveEquivariant

omit [IsAlgClosed k] in
theorem normalizerStable : ∀ n ∈ D.normalizer,
    TauCeti.AlgHom.mapDomain σ n ∈ D.normalizer := by
  let α := TauCeti.AlgHom.mapDomain (A := k) σ
  have hstable : ∀ t ∈ D.torus, α t ∈ D.torus :=
    coordinateImage_stable_of_equivariant H (WeightTorus k D.rank) σ D.torusAut
      D.torusMap D.torusEquivariant
  have hsur : ∀ t ∈ D.torus, ∃ u ∈ D.torus, α u = t := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨u, hu⟩ :=
      (bijective_mapDomain_permutationTorusAut D.weightPerm D.torusAut D.torusOnWeight).2 t
    refine ⟨TauCeti.AlgHom.mapDomain D.torusMap u, ⟨u, rfl⟩, ?_⟩
    change TauCeti.AlgHom.mapDomain σ (TauCeti.AlgHom.mapDomain D.torusMap u) = _
    rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, D.torusEquivariant,
      TauCeti.AlgHom.mapDomain_comp, MonoidHom.comp_apply, hu]
  have hforward : ∀ n ∈ D.normalizer, ∀ t ∈ D.torus,
      α n * t * (α n)⁻¹ ∈ D.torus := by
    intro n hn t ht
    obtain ⟨u, hu, hut⟩ := hsur t ht
    have hconj : n * u * n⁻¹ ∈ D.torus :=
      ((Subgroup.mem_normalizer_iff.mp hn) u).mp hu
    have h := hstable _ hconj
    simpa only [map_mul, map_inv, hut] using h
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨fun ht => hforward n hn t ht, fun ht => ?_⟩
  have h := hforward n⁻¹ (D.normalizer.inv_mem hn)
    (α n * t * (α n)⁻¹) ht
  have he : α n⁻¹ * (α n * t * (α n)⁻¹) * (α n⁻¹)⁻¹ = t := by
    rw [map_inv]
    group
  exact he ▸ h

def fixedPositiveBorel : TauCeti.HopfIdeal k (fixedCoordinate H σ) :=
  D.positiveBorel.map
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom

def fixedNegativeBorel : TauCeti.HopfIdeal k (fixedCoordinate H σ) :=
  D.negativeBorel.map
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom

omit [IsAlgClosed k] in
theorem fixedPositiveBorel_eq : D.fixedPositiveBorel = D.positiveBorel.map
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom := by
  unfold fixedPositiveBorel
  rfl

omit [IsAlgClosed k] in
theorem fixedNegativeBorel_eq : D.fixedNegativeBorel = D.negativeBorel.map
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom := by
  unfold fixedNegativeBorel
  rfl

theorem fixedBorel_intersection_semisimple
    (x : RationalGroup (fixedCoordinate H σ))
    (hxpos : x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup (fixedCoordinate H σ).obj
      D.fixedPositiveBorel (CommAlgCat.of k k))
    (hxneg : x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup (fixedCoordinate H σ).obj
      D.fixedNegativeBorel (CommAlgCat.of k k)) :
    TauCeti.HopfAlgebra.IsSemisimplePoint x := by
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  have hpos : TauCeti.AlgHom.mapDomain q x ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj D.positiveBorel (CommAlgCat.of k k) := by
    exact (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_map_mkQuotient_iff H.obj
      (fixedHopfIdeal H σ) D.positiveBorel (CommAlgCat.of k k) x).mp hxpos
  have hneg : TauCeti.AlgHom.mapDomain q x ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj D.negativeBorel (CommAlgCat.of k k) := by
    exact (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_map_mkQuotient_iff H.obj
      (fixedHopfIdeal H σ) D.negativeBorel (CommAlgCat.of k k) x).mp hxneg
  have htor : TauCeti.AlgHom.mapDomain q x ∈ D.torus := by
    change TauCeti.AlgHom.mapDomain q x ∈ coordinateImage D.torusMap
    rw [← D.opposite]
    exact ⟨hpos, hneg⟩
  obtain ⟨t, ht⟩ := htor
  have hss : TauCeti.HopfAlgebra.IsSemisimplePoint (TauCeti.AlgHom.mapDomain q x) := by
    rw [← ht]
    exact (TauCeti.DiagonalizableGroup.isSemisimplePoint t).mapDomain D.torusMap
  exact (TauCeti.HopfAlgebra.isSemisimplePoint_mapDomain_iff_of_surjective q
    (TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj (fixedHopfIdeal H σ)) x).mp hss

omit [IsAlgClosed k] in
theorem fixed_le_positive_sup_normalizer :
    D.fixed ≤ (D.positiveGroup ⊓ D.fixed) ⊔ (D.normalizer ⊓ D.fixed) := by
  exact fixedSubgroup_le_sup_of_bruhat_coordinates (TauCeti.AlgHom.mapDomain σ)
    D.positiveGroup D.normalizer D.inversion D.inversionPositive
    D.positiveStable D.normalizerStable D.inversionStable D.bruhatCover D.bruhatUnique

omit [IsAlgClosed k] in
theorem torus_stable : ∀ t ∈ D.torus, TauCeti.AlgHom.mapDomain σ t ∈ D.torus := by
  exact coordinateImage_stable_of_equivariant H (WeightTorus k D.rank) σ D.torusAut
    D.torusMap D.torusEquivariant

omit [IsAlgClosed k] in
theorem negative_stable : ∀ u ∈ D.negativeGroup,
    TauCeti.AlgHom.mapDomain σ u ∈ D.negativeGroup := by
  exact coordinateImage_stable_of_equivariant H D.negative σ D.negativeAut
    D.negativeMap.hom D.negativeEquivariant

omit [IsAlgClosed k] in
theorem fixed_positiveBorel_points :
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj D.positiveBorel
      (CommAlgCat.of k k) ⊓ D.fixed =
      (D.torus ⊓ D.fixed) ⊔ (D.positiveGroup ⊓ D.fixed) := by
  rw [D.positiveBorelPoints]
  exact sup_inf_fixedSubgroup_eq (TauCeti.AlgHom.mapDomain σ) D.torus D.positiveGroup
    D.torusNormalizesPositive D.torusDisjointPositive D.torus_stable D.positiveStable

omit [IsAlgClosed k] in
theorem fixed_negativeBorel_points :
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj D.negativeBorel
      (CommAlgCat.of k k) ⊓ D.fixed =
      (D.torus ⊓ D.fixed) ⊔ (D.negativeGroup ⊓ D.fixed) := by
  rw [D.negativeBorelPoints]
  exact sup_inf_fixedSubgroup_eq (TauCeti.AlgHom.mapDomain σ) D.torus D.negativeGroup
    D.torusNormalizesNegative D.torusDisjointNegative D.torus_stable D.negative_stable

omit [IsAlgClosed k] in
theorem cube_of_equivariant_surjective
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H)
    (K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (τ : K →ₐc[k] K)
    (f : H →ₐc[k] K) (hfs : Function.Surjective f)
    (hf : f.comp σ = τ.comp f) :
    (τ.comp τ).comp τ = BialgHom.id k K := by
  apply BialgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := hfs x
  have he : ∀ a, τ (f a) = f (σ a) := fun a =>
    (congrArg (fun g : H →ₐc[k] K => g a) hf).symm
  change τ (τ (τ (f x))) = f x
  rw [he, he, he]
  exact congrArg f (congrArg (fun g : H →ₐc[k] H => g x) hσ)

theorem fixed_factors_connected (h3 : (3 : k) ≠ 0)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    ConnectedSpace (PrimeSpectrum (fixedCoordinate (WeightTorus k D.rank) D.torusAut)) ∧
    ConnectedSpace (PrimeSpectrum (fixedCoordinate D.positive D.positiveAut)) ∧
    ConnectedSpace (PrimeSpectrum (fixedCoordinate D.negative D.negativeAut)) := by
  let := D.positiveSmooth
  let := D.negativeSmooth
  let : ConnectedSpace (PrimeSpectrum D.positive) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace k D.positive.obj
      D.positiveConnected
  let : ConnectedSpace (PrimeSpectrum D.negative) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace k D.negative.obj
      D.negativeConnected
  let : IsDomain D.positive := CFSG.isDomain_of_smooth_of_connected (k := k) D.positive
  let : IsDomain D.negative := CFSG.isDomain_of_smooth_of_connected (k := k) D.negative
  have hP : (D.positiveAut.comp D.positiveAut).comp D.positiveAut = BialgHom.id k _ :=
    cube_of_equivariant_surjective hσ _ _ D.positiveMap.hom D.positiveSurjective D.positiveEquivariant
  have hN : (D.negativeAut.comp D.negativeAut).comp D.negativeAut = BialgHom.id k _ :=
    cube_of_equivariant_surjective hσ _ _ D.negativeMap.hom D.negativeSurjective D.negativeEquivariant
  have hPU : ∀ x : RationalGroup D.positive, TauCeti.HopfAlgebra.IsUnipotentPoint x := by
    intro x
    exact (TauCeti.HopfAlgebra.isUnipotentPoint_mapDomain_iff_of_surjective
      D.positiveMap.hom D.positiveSurjective x).mp (D.positiveUnipotent x)
  have hNU : ∀ x : RationalGroup D.negative, TauCeti.HopfAlgebra.IsUnipotentPoint x := by
    intro x
    exact (TauCeti.HopfAlgebra.isUnipotentPoint_mapDomain_iff_of_surjective
      D.negativeMap.hom D.negativeSurjective x).mp (D.negativeUnipotent x)
  exact ⟨connectedSpace_fixedCoordinate_permutation_torus D.weightPerm D.torusAut D.torusOnWeight,
    connectedSpace_fixedCoordinate_of_unipotent_three D.positive hPU h3 D.positiveAut hP,
    connectedSpace_fixedCoordinate_of_unipotent_three D.negative hNU h3 D.negativeAut hN⟩

omit [IsAlgClosed k] in
theorem fixed_factors_smooth (h3 : (3 : k) ≠ 0)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    Algebra.Smooth k (fixedCoordinate (WeightTorus k D.rank) D.torusAut) ∧
      Algebra.Smooth k (fixedCoordinate D.positive D.positiveAut) ∧
      Algebra.Smooth k (fixedCoordinate D.negative D.negativeAut) := by
  have hT : (D.torusAut.comp D.torusAut).comp D.torusAut = BialgHom.id k _ :=
    cube_of_equivariant_surjective hσ _ _ D.torusMap D.torusSurjective D.torusEquivariant
  have hP : (D.positiveAut.comp D.positiveAut).comp D.positiveAut = BialgHom.id k _ :=
    cube_of_equivariant_surjective hσ _ _ D.positiveMap.hom D.positiveSurjective D.positiveEquivariant
  have hN : (D.negativeAut.comp D.negativeAut).comp D.negativeAut = BialgHom.id k _ :=
    cube_of_equivariant_surjective hσ _ _ D.negativeMap.hom D.negativeSurjective D.negativeEquivariant
  have hTsm : Algebra.Smooth k (WeightTorus k D.rank) := by
    have ht : TauCeti.torusCommHopfAlgProperty k (WeightTorus k D.rank) :=
      (TauCeti.splitTorusCommHopfAlgProperty_coordinateRing k
        (TauCeti.SplitTorus.characterGroup (ULift.{u} (Fin D.rank)))).torus k _
    exact (TauCeti.smoothCommHopfAlgProperty_iff _).mp (ht.smooth k _)
  have hPsm : Algebra.Smooth k D.positive := D.positiveSmooth
  have hNsm : Algebra.Smooth k D.negative := D.negativeSmooth
  let := hTsm
  let := hPsm
  let := hNsm
  exact ⟨smooth_fixedCoordinate_three _ h3 _ hT,
    smooth_fixedCoordinate_three _ h3 _ hP, smooth_fixedCoordinate_three _ h3 _ hN⟩

def fixedTorusMap : (fixedCoordinate H σ).obj ⟶
    (fixedCoordinate (WeightTorus k D.rank) D.torusAut).obj :=
  (fixedCoordinateMap H (WeightTorus k D.rank) σ D.torusAut
    (_root_.CommHopfAlgCat.ofHom D.torusMap) D.torusEquivariant).hom

def fixedPositiveMap : (fixedCoordinate H σ).obj ⟶
    (fixedCoordinate D.positive D.positiveAut).obj :=
  (fixedCoordinateMap H D.positive σ D.positiveAut D.positiveMap D.positiveEquivariant).hom

def fixedNegativeMap : (fixedCoordinate H σ).obj ⟶
    (fixedCoordinate D.negative D.negativeAut).obj :=
  (fixedCoordinateMap H D.negative σ D.negativeAut D.negativeMap D.negativeEquivariant).hom

theorem connectedGenerators_le_component_kernel (h3 : (3 : k) ≠ 0)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    D.connectedGenerators ≤
      ((TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom (fixedCoordinate H σ)
          (CommAlgCat.of k k)).ker).map
        (TauCeti.AlgHom.mapDomain (A := k)
          (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom) := by
  let F := fixedCoordinate H σ
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  let P := ((TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom F
    (CommAlgCat.of k k)).ker).map (TauCeti.AlgHom.mapDomain (A := k) q)
  have hconn := D.fixed_factors_connected h3 hσ
  have htor : D.torus ⊓ D.fixed ≤ P :=
    fixed_image_le_component_kernel H (WeightTorus k D.rank) σ D.torusAut
      (_root_.CommHopfAlgCat.ofHom D.torusMap) D.torusEquivariant D.torusSurjective
      hconn.1
  have hpos : D.positiveGroup ⊓ D.fixed ≤ P :=
    fixed_image_le_component_kernel H D.positive σ D.positiveAut D.positiveMap
      D.positiveEquivariant D.positiveSurjective hconn.2.1
  have hneg : D.negativeGroup ⊓ D.fixed ≤ P :=
    fixed_image_le_component_kernel H D.negative σ D.negativeAut D.negativeMap
      D.negativeEquivariant D.negativeSurjective hconn.2.2
  exact sup_le (sup_le htor hpos) hneg

theorem connectedSpace_fixedCoordinate (h3 : (3 : k) ≠ 0)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H)
    (hN : D.normalizer ⊓ D.fixed ≤ D.connectedGenerators) :
    ConnectedSpace (PrimeSpectrum (fixedCoordinate H σ)) := by
  let F := fixedCoordinate H σ
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  let c := TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom F (CommAlgCat.of k k)
  have hgen : D.fixed ≤ D.connectedGenerators :=
    D.fixed_le_positive_sup_normalizer.trans (sup_le
      ((le_sup_right : D.positiveGroup ⊓ D.fixed ≤
        (D.torus ⊓ D.fixed) ⊔ (D.positiveGroup ⊓ D.fixed)).trans le_sup_left) hN)
  apply connectedSpace_of_componentPointsHom_eq_one F
  intro x
  have hx : TauCeti.AlgHom.mapDomain q x ∈ D.fixed := fixedCoordinate_point_fixed H σ x
  obtain ⟨y, hy, hxy⟩ := D.connectedGenerators_le_component_kernel h3 hσ (hgen hx)
  have heq : y = x := TauCeti.CommHopfAlgCat.quotientPointsHom_injective H.obj
    (fixedHopfIdeal H σ) (CommAlgCat.of k k) hxy
  exact heq ▸ hy

theorem connectedSpace_fixedPositiveBorel (h3 : (3 : k) ≠ 0)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    ConnectedSpace (PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.quotient
      (fixedCoordinate H σ) D.fixedPositiveBorel)) := by
  let F := fixedCoordinate H σ
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  have ht := D.fixed_factors_smooth h3 hσ
  let := ht.1
  let := ht.2.1
  let : IsReduced (fixedCoordinate (WeightTorus k D.rank) D.torusAut) :=
    TauCeti.isReduced_of_smooth k _
  let : IsReduced (fixedCoordinate D.positive D.positiveAut) := TauCeti.isReduced_of_smooth k _
  apply connectedSpace_closed_subgroup_of_sup_images F
    (fixedCoordinate (WeightTorus k D.rank) D.torusAut) (fixedCoordinate D.positive D.positiveAut)
    D.fixedPositiveBorel D.fixedTorusMap D.fixedPositiveMap
    (D.fixed_factors_connected h3 hσ).1 (D.fixed_factors_connected h3 hσ).2.1
  apply Subgroup.map_injective
    (TauCeti.CommHopfAlgCat.quotientPointsHom_injective H.obj (fixedHopfIdeal H σ) (CommAlgCat.of k k))
  have hleft : (TauCeti.CommHopfAlgCat.quotientPointsSubgroup F.obj D.fixedPositiveBorel
        (CommAlgCat.of k k)).map (TauCeti.AlgHom.mapDomain (A := k) q) =
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj D.positiveBorel
        (CommAlgCat.of k k) ⊓ D.fixed := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_map_mkQuotient_iff H.obj
        (fixedHopfIdeal H σ) D.positiveBorel (CommAlgCat.of k k) y).mp hy,
        fixedCoordinate_point_fixed H σ y⟩
    · rintro ⟨hxB, hxF⟩
      have hx : x ∈ (TauCeti.AlgHom.mapDomain (A := k) q).range := by
        rw [fixedCoordinate_points_range]
        exact hxF
      obtain ⟨y, rfl⟩ := hx
      exact ⟨y, (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_map_mkQuotient_iff H.obj
        (fixedHopfIdeal H σ) D.positiveBorel (CommAlgCat.of k k) y).mpr hxB, rfl⟩
  change (TauCeti.CommHopfAlgCat.quotientPointsSubgroup F.obj D.fixedPositiveBorel
      (CommAlgCat.of k k)).map (TauCeti.AlgHom.mapDomain (A := k) q) = _
  rw [hleft, Subgroup.map_sup]
  have htor := fixedCoordinateMap_range_map_eq_inf H (WeightTorus k D.rank) σ D.torusAut
    (_root_.CommHopfAlgCat.ofHom D.torusMap) D.torusEquivariant D.torusSurjective
  have hpos := fixedCoordinateMap_range_map_eq_inf H D.positive σ D.positiveAut
    D.positiveMap D.positiveEquivariant D.positiveSurjective
  change (coordinateImage D.fixedTorusMap.hom).map
      (TauCeti.AlgHom.mapDomain (A := k) q) = D.torus ⊓ D.fixed at htor
  change (coordinateImage D.fixedPositiveMap.hom).map
      (TauCeti.AlgHom.mapDomain (A := k) q) = D.positiveGroup ⊓ D.fixed at hpos
  change (TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj D.positiveBorel
      (CommAlgCat.of k k) ⊓ D.fixed) =
    (coordinateImage (H := F) (K := fixedCoordinate (WeightTorus k D.rank) D.torusAut)
      D.fixedTorusMap.hom).map (TauCeti.AlgHom.mapDomain (H₁ := H) (H₂ := F) (A := k) q) ⊔
    (coordinateImage (H := F) (K := fixedCoordinate D.positive D.positiveAut)
      D.fixedPositiveMap.hom).map (TauCeti.AlgHom.mapDomain (H₁ := H) (H₂ := F) (A := k) q)
  rw [htor, hpos]
  exact D.fixed_positiveBorel_points

theorem connectedSpace_fixedNegativeBorel (h3 : (3 : k) ≠ 0)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    ConnectedSpace (PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.quotient
      (fixedCoordinate H σ) D.fixedNegativeBorel)) := by
  let F := fixedCoordinate H σ
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  have ht := D.fixed_factors_smooth h3 hσ
  let := ht.1
  let := ht.2.2
  let : IsReduced (fixedCoordinate (WeightTorus k D.rank) D.torusAut) :=
    TauCeti.isReduced_of_smooth k _
  let : IsReduced (fixedCoordinate D.negative D.negativeAut) := TauCeti.isReduced_of_smooth k _
  apply connectedSpace_closed_subgroup_of_sup_images F
    (fixedCoordinate (WeightTorus k D.rank) D.torusAut) (fixedCoordinate D.negative D.negativeAut)
    D.fixedNegativeBorel D.fixedTorusMap D.fixedNegativeMap
    (D.fixed_factors_connected h3 hσ).1 (D.fixed_factors_connected h3 hσ).2.2
  apply Subgroup.map_injective
    (TauCeti.CommHopfAlgCat.quotientPointsHom_injective H.obj (fixedHopfIdeal H σ) (CommAlgCat.of k k))
  have hleft : (TauCeti.CommHopfAlgCat.quotientPointsSubgroup F.obj D.fixedNegativeBorel
        (CommAlgCat.of k k)).map (TauCeti.AlgHom.mapDomain (A := k) q) =
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj D.negativeBorel
        (CommAlgCat.of k k) ⊓ D.fixed := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_map_mkQuotient_iff H.obj
        (fixedHopfIdeal H σ) D.negativeBorel (CommAlgCat.of k k) y).mp hy,
        fixedCoordinate_point_fixed H σ y⟩
    · rintro ⟨hxB, hxF⟩
      have hx : x ∈ (TauCeti.AlgHom.mapDomain (A := k) q).range := by
        rw [fixedCoordinate_points_range]
        exact hxF
      obtain ⟨y, rfl⟩ := hx
      exact ⟨y, (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_map_mkQuotient_iff H.obj
        (fixedHopfIdeal H σ) D.negativeBorel (CommAlgCat.of k k) y).mpr hxB, rfl⟩
  change (TauCeti.CommHopfAlgCat.quotientPointsSubgroup F.obj D.fixedNegativeBorel
      (CommAlgCat.of k k)).map (TauCeti.AlgHom.mapDomain (A := k) q) = _
  rw [hleft, Subgroup.map_sup]
  have htor := fixedCoordinateMap_range_map_eq_inf H (WeightTorus k D.rank) σ D.torusAut
    (_root_.CommHopfAlgCat.ofHom D.torusMap) D.torusEquivariant D.torusSurjective
  have hneg := fixedCoordinateMap_range_map_eq_inf H D.negative σ D.negativeAut
    D.negativeMap D.negativeEquivariant D.negativeSurjective
  change (coordinateImage D.fixedTorusMap.hom).map
      (TauCeti.AlgHom.mapDomain (A := k) q) = D.torus ⊓ D.fixed at htor
  change (coordinateImage D.fixedNegativeMap.hom).map
      (TauCeti.AlgHom.mapDomain (A := k) q) = D.negativeGroup ⊓ D.fixed at hneg
  change (TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj D.negativeBorel
      (CommAlgCat.of k k) ⊓ D.fixed) =
    (coordinateImage (H := F) (K := fixedCoordinate (WeightTorus k D.rank) D.torusAut)
      D.fixedTorusMap.hom).map (TauCeti.AlgHom.mapDomain (H₁ := H) (H₂ := F) (A := k) q) ⊔
    (coordinateImage (H := F) (K := fixedCoordinate D.negative D.negativeAut)
      D.fixedNegativeMap.hom).map (TauCeti.AlgHom.mapDomain (H₁ := H) (H₂ := F) (A := k) q)
  rw [htor, hneg]
  exact D.fixed_negativeBorel_points

theorem positiveBorel_stable : ∀ x ∈ D.positiveBorel, σ x ∈ D.positiveBorel := by
  have hsm : Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.quotient H D.positiveBorel) :=
    (TauCeti.smoothCommHopfAlgProperty_iff _).mp
      ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H D.positiveBorel).mp D.isPositiveBorel).2.1.smooth
  let := hsm
  let : IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient H D.positiveBorel) :=
    TauCeti.isReduced_of_smooth k _
  apply mem_ideal_map_of_points_stable H D.positiveBorel σ
  intro x hx
  rw [D.positiveBorelPoints] at hx ⊢
  have hsup : (D.torus ⊔ D.positiveGroup).map (TauCeti.AlgHom.mapDomain σ) ≤
      D.torus ⊔ D.positiveGroup := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨t, ht, rfl⟩
      exact Subgroup.mem_sup_left (D.torus_stable t ht)
    · rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.mem_sup_right (D.positiveStable u hu)
  exact hsup ⟨x, hx, rfl⟩

theorem negativeBorel_stable : ∀ x ∈ D.negativeBorel, σ x ∈ D.negativeBorel := by
  have hsm : Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.quotient H D.negativeBorel) :=
    (TauCeti.smoothCommHopfAlgProperty_iff _).mp
      ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H D.negativeBorel).mp D.isNegativeBorel).2.1.smooth
  let := hsm
  let : IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient H D.negativeBorel) :=
    TauCeti.isReduced_of_smooth k _
  apply mem_ideal_map_of_points_stable H D.negativeBorel σ
  intro x hx
  rw [D.negativeBorelPoints] at hx ⊢
  have hsup : (D.torus ⊔ D.negativeGroup).map (TauCeti.AlgHom.mapDomain σ) ≤
      D.torus ⊔ D.negativeGroup := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨t, ht, rfl⟩
      exact Subgroup.mem_sup_left (D.torus_stable t ht)
    · rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.mem_sup_right (D.negative_stable u hu)
  exact hsup ⟨x, hx, rfl⟩

theorem smooth_fixedPositiveBorel (h3 : (3 : k) ≠ 0)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.quotient
      (fixedCoordinate H σ) D.fixedPositiveBorel) := by
  let B := TauCeti.FiniteTypeCommHopfAlgCat.quotient H D.positiveBorel
  let τ := quotientCoordinateEnd H D.positiveBorel σ D.positiveBorel_stable
  have he := quotientCoordinateEnd_equivariant H D.positiveBorel σ D.positiveBorel_stable
  have hτ := cube_of_equivariant_surjective hσ B τ
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H D.positiveBorel).hom.hom
    (TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj D.positiveBorel) he
  have hsm : Algebra.Smooth k B :=
    (TauCeti.smoothCommHopfAlgProperty_iff _).mp
      ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H D.positiveBorel).mp D.isPositiveBorel).2.1.smooth
  let := hsm
  let : Algebra.Smooth k (fixedCoordinate B τ) := smooth_fixedCoordinate_three B h3 τ hτ
  exact Algebra.Smooth.of_equiv (fixedCoordinateQuotientAlgEquiv H D.positiveBorel σ τ he)

theorem smooth_fixedNegativeBorel (h3 : (3 : k) ≠ 0)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.quotient
      (fixedCoordinate H σ) D.fixedNegativeBorel) := by
  let B := TauCeti.FiniteTypeCommHopfAlgCat.quotient H D.negativeBorel
  let τ := quotientCoordinateEnd H D.negativeBorel σ D.negativeBorel_stable
  have he := quotientCoordinateEnd_equivariant H D.negativeBorel σ D.negativeBorel_stable
  have hτ := cube_of_equivariant_surjective hσ B τ
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H D.negativeBorel).hom.hom
    (TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj D.negativeBorel) he
  have hsm : Algebra.Smooth k B :=
    (TauCeti.smoothCommHopfAlgProperty_iff _).mp
      ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H D.negativeBorel).mp D.isNegativeBorel).2.1.smooth
  let := hsm
  let : Algebra.Smooth k (fixedCoordinate B τ) := smooth_fixedCoordinate_three B h3 τ hτ
  exact Algebra.Smooth.of_equiv (fixedCoordinateQuotientAlgEquiv H D.negativeBorel σ τ he)

theorem fixedPositiveBorel_isBorelCandidate (h3 : (3 : k) ≠ 0)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    TauCeti.HopfIdeal.IsBorelCandidate k (fixedCoordinate H σ) D.fixedPositiveBorel := by
  apply TauCeti.HopfIdeal.IsBorelCandidate.mk
  · exact (TauCeti.smoothCommHopfAlgProperty_iff _).mpr (D.smooth_fixedPositiveBorel h3 hσ)
  · exact (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).mpr
      (D.connectedSpace_fixedPositiveBorel h3 hσ)
  · exact geometricallySolvable_intersection_quotient H (fixedHopfIdeal H σ) D.positiveBorel
      ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H D.positiveBorel).mp
        D.isPositiveBorel).2.1.geometricallySolvable

theorem fixedNegativeBorel_isBorelCandidate (h3 : (3 : k) ≠ 0)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    TauCeti.HopfIdeal.IsBorelCandidate k (fixedCoordinate H σ) D.fixedNegativeBorel := by
  apply TauCeti.HopfIdeal.IsBorelCandidate.mk
  · exact (TauCeti.smoothCommHopfAlgProperty_iff _).mpr (D.smooth_fixedNegativeBorel h3 hσ)
  · exact (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).mpr
      (D.connectedSpace_fixedNegativeBorel h3 hσ)
  · exact geometricallySolvable_intersection_quotient H (fixedHopfIdeal H σ) D.negativeBorel
      ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H D.negativeBorel).mp
        D.isNegativeBorel).2.1.geometricallySolvable

end StableTriangularCoordinates

end CFSG.LieType.AlgebraicGroups
