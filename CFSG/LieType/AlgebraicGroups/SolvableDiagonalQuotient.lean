module

public import CFSG.LieType.AlgebraicGroups.TorusTriangularRepresentation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
public import TauCeti.Algebra.Bialgebra.GroupLike.Torsion
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Character
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public noncomputable section

open CategoryTheory WithConv TauCeti
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem torus_of_groupLikeSetSpan_eq_top
    (H : FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)]
    (hspan : Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ = ⊤) :
    torusCommHopfAlgProperty k H := by
  let : Group.FG (_root_.GroupLike k H) :=
    TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top k H inferInstance hspan
  let : IsMulTorsionFree (_root_.GroupLike k H) :=
    isMulTorsionFree_groupLike_of_isReduced_of_connectedSpace k H
  let G := FGCommGrpCat.of (_root_.GroupLike k H)
  have hspan' := (Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top (R := k) (C := H)).mp hspan
  let e : (DiagonalizableGroup.coordinateRing k G).obj ≅ H.obj :=
    _root_.CommHopfAlgCat.isoMk (TauCeti.GroupLike.evaluationBialgEquiv k H hspan') ≪≫
      _root_.CommHopfAlgCat.ofIsoSelf H.obj
  exact splitTorusCommHopfAlgProperty.torus k H
    ((splitTorusCommHopfAlgProperty k).prop_of_iso
      (ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty k) e)
      (splitTorusCommHopfAlgProperty_coordinateRing k G))

theorem torus_image_of_groupAlgebra
    (H : FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)]
    {M : Type u} [CommGroup M] [Group.FG M]
    (f : MonoidAlgebra k M →ₐc[k] H) :
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.image (_root_.CommHopfAlgCat.ofHom f))) := by
  let F := _root_.CommHopfAlgCat.ofHom f
  let Q := FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.image F)
  have hc : geometricallyConnectedCommHopfAlgProperty k Q.obj :=
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k H.obj).mpr
      inferInstance |>.image F
  have hsm : smoothCommHopfAlgProperty k Q.obj := smoothCommHopfAlgProperty.image F
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k H.obj)
  let : IsReduced Q := (smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed k Q.obj).mp hsm
  let : ConnectedSpace (PrimeSpectrum Q) := hc.connectedSpace k Q.obj
  apply torus_of_groupLikeSetSpan_eq_top Q
  exact TauCeti.GroupLike.groupLikeSetSpan_eq_top_of_surjective
    (CommHopfAlgCat.mkImage F).hom (CommHopfAlgCat.mkImage_surjective F)
    (TauCeti.MonoidAlgebra.groupLikeSetSpan_eq_top k M)

def triangularDiagonalCharacterMap
    (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hdiag : ∀ i, IsGroupLikeElem k (Comodule.coefficientMatrix (C := H) b i i)) :
    MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐc[k] H :=
  (TauCeti.GroupLike.evaluationBialgHom k H).comp
    (MonoidAlgebra.mapDomainBialgHom k
      (TauCeti.freeAbelianCharEquiv.symm
        (fun i : ULift.{u} (Fin n) => (⟨Comodule.coefficientMatrix (C := H) b i.down i.down,
          hdiag i.down⟩ : _root_.GroupLike k H))))

omit [IsAlgClosed k] in
@[simp] theorem triangularDiagonalCharacterMap_single
    (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hdiag : ∀ i, IsGroupLikeElem k (Comodule.coefficientMatrix (C := H) b i i))
    (i : Fin n) :
    triangularDiagonalCharacterMap H b hdiag
      (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1) =
        Comodule.coefficientMatrix (C := H) b i i := by
  simp only [triangularDiagonalCharacterMap, BialgHom.comp_apply,
    MonoidAlgebra.mapDomainBialgHom_single,
    TauCeti.freeAbelianCharEquiv_symm_apply_ofAdd_single,
    TauCeti.GroupLike.evaluationBialgHom_single, one_smul]

omit [IsAlgClosed k] in
theorem diagonal_coefficient_mem_image
    (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hdiag : ∀ i, IsGroupLikeElem k (Comodule.coefficientMatrix (C := H) b i i))
    (i : Fin n) :
    Comodule.coefficientMatrix (C := H) b i i ∈
      (CommHopfAlgCat.imageι
        (_root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag))).hom.toAlgHom.range := by
  let F := _root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag)
  refine ⟨(CommHopfAlgCat.mkImage F).hom
    (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1), ?_⟩
  change (CommHopfAlgCat.imageι F).hom ((CommHopfAlgCat.mkImage F).hom
    (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1)) = _
  exact (CommHopfAlgCat.imageι_mkImage_apply F _).trans
    (triangularDiagonalCharacterMap_single H b hdiag i)

omit [IsAlgClosed k] in
theorem exists_groupLike_diagonal_lift
    (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hdiag : ∀ i, IsGroupLikeElem k (Comodule.coefficientMatrix (C := H) b i i)) :
    ∃ c : Fin n → _root_.GroupLike k
        (CommHopfAlgCat.image (_root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag))),
      ∀ i, (CommHopfAlgCat.imageι
        (_root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag))).hom (c i) =
          Comodule.coefficientMatrix (C := H) b i i := by
  let F := _root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag)
  let c : Fin n → _root_.GroupLike k (CommHopfAlgCat.image F) := fun i =>
    ⟨(CommHopfAlgCat.mkImage F).hom
      (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1),
      (MonoidAlgebra.isGroupLikeElem_single_one _).map (CommHopfAlgCat.mkImage F).hom⟩
  refine ⟨c, fun i => ?_⟩
  have hc : (c i : CommHopfAlgCat.image F) = (CommHopfAlgCat.mkImage F).hom
      (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1) := rfl
  rw [hc]
  exact (CommHopfAlgCat.imageι_mkImage_apply F _).trans
    (triangularDiagonalCharacterMap_single H b hdiag i)

omit [IsAlgClosed k] in
theorem diagonal_antipode_mem_image
    (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hdiag : ∀ i, IsGroupLikeElem k (Comodule.coefficientMatrix (C := H) b i i))
    (i : Fin n) :
    HopfAlgebra.antipodeAlgHom k H (Comodule.coefficientMatrix (C := H) b i i) ∈
      (CommHopfAlgCat.imageι
        (_root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag))).hom.toAlgHom.range := by
  let F := _root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag)
  let p := (CommHopfAlgCat.imageι F).hom
  have hc : Comodule.coefficientMatrix (C := H) b i i ∈ p.toAlgHom.range :=
    diagonal_coefficient_mem_image H b hdiag i
  obtain ⟨c, hc⟩ := hc
  refine ⟨HopfAlgebra.antipodeAlgHom k (CommHopfAlgCat.image F) c, ?_⟩
  change p (HopfAlgebra.antipode k c) =
    HopfAlgebra.antipode k (Comodule.coefficientMatrix (C := H) b i i)
  exact (BialgHomClass.map_antipode p c).trans (congrArg (HopfAlgebra.antipode k) hc)

theorem surjective_diagonal_image_restriction_of_torus
    (H T : FiniteTypeCommHopfAlgCat.{u,u} k) (hT : torusCommHopfAlgProperty k T)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hupper : (Comodule.coefficientMatrix (C := H) b).IsUpperTriangular)
    (hdiag : ∀ i, IsGroupLikeElem k (Comodule.coefficientMatrix (C := H) b i i))
    (hfaith : Function.Surjective (Comodule.coordinateBialgHom (H := H) b))
    (q : H →ₐc[k] T) (hq : Function.Surjective q) :
    Function.Surjective (q.comp (CommHopfAlgCat.imageι
      (_root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag))).hom) := by
  let F := _root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag)
  let D := FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.image F)
  exact surjective_comp_of_range_diagonal_coefficients H T D hT b hupper hfaith q hq
    (CommHopfAlgCat.imageι F).hom (diagonal_coefficient_mem_image H b hdiag)
    (diagonal_antipode_mem_image H b hdiag)

omit [IsAlgClosed k] in
theorem triangularDiagonalCharacterMap_points_eq_one_iff
    (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hdiag : ∀ i, IsGroupLikeElem k (Comodule.coefficientMatrix (C := H) b i i))
    (g : WithConv (H →ₐ[k] k)) :
    AlgHom.mapDomain (triangularDiagonalCharacterMap H b hdiag) g = 1 ↔
      ∀ i, g.ofConv (Comodule.coefficientMatrix (C := H) b i i) = 1 := by
  let E := SplitTorus.pointsMulEquiv
    (R := k) (σ := ULift.{u} (Fin n)) (A := k)
  rw [← E.injective.eq_iff, map_one]
  constructor
  · intro h i
    have hi := congrArg (fun c : ULift.{u} (Fin n) → kˣ => (c (ULift.up i) : k)) h
    simpa [E, SplitTorus.pointsMulEquiv_apply_coe, AlgHom.mapDomain_apply,
      triangularDiagonalCharacterMap_single] using hi
  · intro h
    funext i
    cases i with
    | up i =>
      apply Units.ext
      simpa [E, SplitTorus.pointsMulEquiv_apply_coe, AlgHom.mapDomain_apply,
        triangularDiagonalCharacterMap_single] using h i

omit [IsAlgClosed k] in
theorem triangularDiagonalImageMap_points_eq_one_iff
    (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hdiag : ∀ i, IsGroupLikeElem k (Comodule.coefficientMatrix (C := H) b i i))
    (g : WithConv (H →ₐ[k] k)) :
    AlgHom.mapDomain (CommHopfAlgCat.imageι
      (_root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag))).hom g = 1 ↔
      ∀ i, g.ofConv (Comodule.coefficientMatrix (C := H) b i i) = 1 := by
  let a := triangularDiagonalCharacterMap H b hdiag
  let F := _root_.CommHopfAlgCat.ofHom a
  let T := FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.image F)
  let p : T →ₐc[k] H := (CommHopfAlgCat.imageι F).hom
  rw [← triangularDiagonalCharacterMap_points_eq_one_iff H b hdiag g]
  let q := (CommHopfAlgCat.mkImage F).hom
  have hq : Function.Injective (AlgHom.mapDomain (A := k) q) := by
    intro x y hxy
    apply WithConv.ext
    ext z
    obtain ⟨a, rfl⟩ := CommHopfAlgCat.mkImage_surjective F z
    have h := congrArg (fun t => t.ofConv a) hxy
    simpa only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom] using h
  have hsquare : p.comp q = a := by
    exact congrArg (fun f : _root_.CommHopfAlgCat.of k
      (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) ⟶ H.obj => f.hom)
        (CommHopfAlgCat.mkImage_comp_imageι F)
  have hpoint : AlgHom.mapDomain q (AlgHom.mapDomain p g) = AlgHom.mapDomain a g := by
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    change g.ofConv (p (q x)) = g.ofConv (a x)
    exact congrArg (fun z : H => g.ofConv z) (DFunLike.congr_fun hsquare x)
  constructor
  · intro h
    rw [← hpoint, h, map_one]
  · intro h
    apply hq
    rw [hpoint, h, map_one]

theorem isUnipotentPoint_iff_diagonal_coefficients_eq_one
    (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hfaith : Function.Surjective (Comodule.coordinateBialgHom (H := H) b))
    (hupper : (Comodule.coefficientMatrix (C := H) b).IsUpperTriangular)
    (hdiag : ∀ i, IsGroupLikeElem k (Comodule.coefficientMatrix (C := H) b i i))
    (g : WithConv (H →ₐ[k] k)) :
    HopfAlgebra.IsUnipotentPoint g ↔
      ∀ i, g.ofConv (Comodule.coefficientMatrix (C := H) b i i) = 1 := by
  constructor
  · intro hg i
    exact hg.apply_groupLike_eq_one ⟨_, hdiag i⟩
  · intro hg
    let : Module.Finite k V := Module.Finite.of_basis b
    let : Module.Free k V := Module.Free.of_basis b
    let M := FGComoduleCat.of (R := k) (C := H) V
    have hfaith' : Comodule.IsFaithful (k := k) (H := H) (V := V) :=
      (Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).mpr
        ((Comodule.isClosedImmersion_coordinateGroupSchemeHom_iff b).mpr hfaith)
    apply (HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful M hfaith' g).mpr
    apply LinearMap.GeneralLinearGroup.isUnipotent_of_charpoly_eq (n := n)
    have hact : (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g) :
        Module.End k (k ⊗[k] M)) = Comodule.endOfPoint M g.ofConv := by
      exact Comodule.pointsAction_toLinearMap M g
    rw [hact]
    change (Comodule.endOfPoint V g.ofConv).charpoly = (Polynomial.X - 1) ^ n
    rw [← LinearMap.charpoly_toMatrix (Comodule.endOfPoint V g.ofConv) (b.baseChange k),
      Comodule.toMatrix_endOfPoint]
    have htri : ((Comodule.coefficientMatrix (C := H) b).map g.ofConv).IsUpperTriangular := by
      intro i j hji
      simp only [Matrix.map_apply, hupper hji, map_zero]
    rw [Matrix.charpoly_of_isUpperTriangular _ htri]
    simp [Matrix.map_apply, hg]


end CFSG.LieType.AlgebraicGroups
