module

public import CFSG.LieType.AlgebraicGroups.ReductiveDescent
public import CFSG.LieType.AlgebraicGroups.MatrixComponentQuotient
public import CFSG.LieType.AlgebraicGroups.ExactAffineRealization
public import CFSG.LieType.Chevalley.NoncentralNormalSolvable
public import CFSG.LieType.Chevalley.BabyPrereqPerfectAwayFromTwo
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Solvable

public noncomputable section

open WithConv
open scoped CFSG.ConvolutionPoints
namespace CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

theorem smooth_geometricallyConnected_coordinate_adjointGroup (τ : Tag) (k : Type)
    [Field k] [IsAlgClosed k] :
    Algebra.Smooth k (MatrixComponents.coordinateHopf (adjointGroup τ k)) ∧
      TauCeti.geometricallyConnectedCommHopfAlgProperty k
        (MatrixComponents.coordinateHopf (adjointGroup τ k)).obj := by
  have h := (exceptional_Lang_exact_affine_group_realization k τ).1.2.1
  refine ⟨h.smooth.1, ?_⟩
  apply (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).2
  exact h.connectedSpace

theorem eq_bot_of_normal_of_isSolvable_adjointGroup (τ : Tag) (K : Type) [Field K]
    (hK : (3 : ℕ∞) ≤ ENat.card K) (M : Subgroup (adjointGroup τ K)) [M.Normal]
    [Group.IsSolvable M] : M = ⊥ := by
  by_contra hM
  have hnc : ¬M ≤ Subgroup.center (adjointGroup τ K) := by
    rw [center_adjointGroup_eq_bot_field τ K, le_bot_iff]
    exact hM
  obtain ⟨-, hsol, -⟩ := noncentral_normal_solvable_quotient τ K M hnc
  have : Group.IsSolvable (adjointGroup τ K ⧸ M) := hsol
  have hG : Group.IsSolvable (adjointGroup τ K) :=
    solvable_of_ker_le_range M.subtype (QuotientGroup.mk' M) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hperf := generated_group_perfect_away_from_two τ K hK
  have htop : ∀ n, derivedSeries (adjointGroup τ K) n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, hperf]
  obtain ⟨n, hn⟩ := hG.solvable
  rw [htop n] at hn
  exact hM (eq_bot_iff.mpr (le_top.trans hn.le))

theorem eq_augmentation_of_normal_unipotent_coordinate_adjointGroup
    (τ : Tag) (k : Type) [Field k] [IsAlgClosed k]
    (I : TauCeti.HopfIdeal (AlgebraicClosure k)
      (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
        (MatrixComponents.coordinateHopf (adjointGroup τ k))))
    (hI : I.IsNormal)
    (hconn : TauCeti.geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
          (MatrixComponents.coordinateHopf (adjointGroup τ k))) I).obj)
    (hU : TauCeti.smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k)
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
          (MatrixComponents.coordinateHopf (adjointGroup τ k))) I)) :
    I = TauCeti.HopfIdeal.augmentation (AlgebraicClosure k)
      (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
        (MatrixComponents.coordinateHopf (adjointGroup τ k))) := by
  classical
  let H := MatrixComponents.coordinateHopf (adjointGroup τ k)
  let K' := AlgebraicClosure k
  let B := TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := K') H
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient B I
  let A := CommAlgCat.of K' K'
  let : Group (TauCeti.HopfAlgebra.points (R := K') (H := B.obj) A : Type) :=
    TauCeti.AlgHom.instGroup
  let S := TauCeti.CommHopfAlgCat.quotientPointsSubgroup B.obj I A
  have hSnormal := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_normal B.obj I hI A
  have hsu := (TauCeti.smoothUnipotentCommHopfAlgProperty_iff K' Q).mp hU
  have : Algebra.FiniteType K' (TauCeti.CommHopfAlgCat.quotient B.obj I) :=
    TauCeti.FiniteTypeCommHopfAlgCat.finiteType Q
  have hgeo : TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty K'
      (CommHopfAlgCat.of K' (TauCeti.CommHopfAlgCat.quotient B.obj I)) :=
    (TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty_iff K' _).mpr hsu.2
  have hsolvΩ := TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.geometricallySolvable hgeo
  rw [TauCeti.geometricallySolvablePointsCommHopfAlgProperty_iff] at hsolvΩ
  let PQ := TauCeti.HopfAlgebra.points (R := K') (H := TauCeti.CommHopfAlgCat.quotient B.obj I) A
  let : Group (PQ : Type) := TauCeti.AlgHom.instGroup
  let ι : (PQ : Type) →*
      WithConv (TauCeti.CommHopfAlgCat.quotient B.obj I →ₐ[K'] AlgebraicClosure K') :=
    TauCeti.AlgHom.mapValue (Algebra.ofId K' (AlgebraicClosure K'))
  have hι : Function.Injective ι := by
    intro f g hfg
    apply WithConv.ext
    ext x
    have h := congrArg (fun φ => φ.ofConv x) hfg
    simp only [ι] at h
    rw [TauCeti.AlgHom.mapValue_apply, TauCeti.AlgHom.mapValue_apply, WithConv.ofConv_toConv,
      WithConv.ofConv_toConv, AlgHom.comp_apply, AlgHom.comp_apply, Algebra.ofId_apply,
      Algebra.ofId_apply] at h
    exact (algebraMap K' (AlgebraicClosure K')).injective h
  have : Group.IsSolvable (PQ : Type) := solvable_of_solvable_injective hι
  let f := (TauCeti.CommHopfAlgCat.quotientPointsHom B.obj I A).hom
  have : Group.IsSolvable S := solvable_of_surjective f.rangeRestrict_surjective
  have hG : IsPointClosed k
      (transportPoints (modGLPoint τ k) (adjointGroup τ k : Set (ModGL τ k))) := by
    rw [transportPoints_modGLPoint]
    exact (exceptional_Lang_exact_affine_group_realization k τ).1.1
  let e := (ReductiveDescent.baseChangePointsMulEquivOfIsAlgClosed H).trans
    (MatrixComponents.coordinatePointsMulEquiv (adjointGroup τ k) hG)
  let φ : (TauCeti.HopfAlgebra.points (R := K') (H := B.obj) A : Type) →* adjointGroup τ k :=
    MonoidHom.mk' (fun x => e x) fun a b => e.map_mul a b
  have hφs : Function.Surjective φ := e.surjective
  have hφi : Function.Injective φ := e.injective
  let S' := S.map φ
  have : S'.Normal := hSnormal.map φ hφs
  have : Group.IsSolvable S' := solvable_of_surjective (φ.subgroupMap_surjective S)
  have hk3 : (3 : ℕ∞) ≤ ENat.card k := by
    rw [ENat.card_eq_top_of_infinite]
    exact le_top
  have hS' : S' = ⊥ := eq_bot_of_normal_of_isSolvable_adjointGroup τ k hk3 S'
  have hS : S = ⊥ := (Subgroup.map_eq_bot_iff_of_injective S hφi).mp hS'
  have hfin : (TauCeti.CommHopfAlgCat.quotientPointsSubgroup B.obj I A :
      Set (WithConv (B →ₐ[K'] K'))).Finite := by
    change (S : Set (WithConv (B →ₐ[K'] K'))).Finite
    rw [hS]
    exact Set.finite_singleton 1
  have hconn' : ConnectedSpace (PrimeSpectrum Q) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace K' Q.obj hconn
  have hred : IsReduced Q :=
    (TauCeti.smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed K' Q.obj).mp
      ((TauCeti.smoothCommHopfAlgProperty_iff _).mpr hsu.1)
  exact ReductiveDescent.eq_augmentation_of_finite_quotientPoints B I hconn' hred hfin

theorem reductive_coordinate_adjointGroup (τ : Tag) (k : Type) [Field k] [IsAlgClosed k] :
    TauCeti.reductiveCommHopfAlgProperty k
      (MatrixComponents.coordinateHopf (adjointGroup τ k)) := by
  rw [TauCeti.reductiveCommHopfAlgProperty_iff]
  have hgeometry := smooth_geometricallyConnected_coordinate_adjointGroup τ k
  exact ⟨hgeometry.1, hgeometry.2,
    eq_augmentation_of_normal_unipotent_coordinate_adjointGroup τ k⟩

end CFSG.LieType.AlgebraicGroups
