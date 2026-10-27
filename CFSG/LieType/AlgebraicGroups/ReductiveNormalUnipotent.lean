module

public import CFSG.LieType.AlgebraicGroups.ReducedIdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Reduced
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Naturality
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic
public import TauCeti.RingTheory.FiniteType.FiniteRange
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed

public noncomputable section
open WithConv CategoryTheory
namespace CFSG.LieType.AlgebraicGroups.CanonicalReductive
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem eq_augmentation_of_reductive_normal_unipotent
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : I.IsNormal)
    (hconn : ConnectedSpace (PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I)))
    (hred : IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I))
    (hu : ∀ x : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I →ₐ[k] k),
      TauCeti.HopfAlgebra.IsUnipotentPoint x) :
    I = TauCeti.HopfIdeal.augmentation k M := by
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient M I
  have hsm : Algebra.Smooth k Q := by
    exact (TauCeti.smoothCommHopfAlgProperty_iff Q.obj).mp
      ((TauCeti.smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed k Q.obj).mpr hred)
  have hU : TauCeti.smoothUnipotentCommHopfAlgProperty k Q :=
    (TauCeti.smoothUnipotentCommHopfAlgProperty.iff_smooth_and_forall_isUnipotentPoint
      (A := Q) k).mpr ⟨hsm, hu⟩
  have hQconn : TauCeti.geometricallyConnectedCommHopfAlgProperty k Q.obj :=
    (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k Q.obj).mpr hconn
  have hcan : TauCeti.HopfIdeal.IsUnipotentRadicalCandidate M I :=
    TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.mk hI hQconn hU
  have hle := TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_le M I hcan
  rw [hM.unipotentRadicalDefiningIdeal_eq_augmentation] at hle
  exact le_antisymm (TauCeti.HopfIdeal.le_augmentation k M I) hle

theorem finite_quotientPointsSubgroup_of_reductive_normal_unipotent
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : I.IsNormal)
    (hu : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
      TauCeti.HopfAlgebra.IsUnipotentPoint x) :
    (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
      Set (WithConv (M →ₐ[k] k))).Finite := by
  let : Algebra.Smooth k M := hM.smooth
  let : IsReduced M := TauCeti.isReduced_of_smooth k M
  obtain ⟨J,hJn,hJconn,hJred,hJI,hJfi⟩ :=
    ReductiveDescent.exists_reduced_identityComponent_of_isReduced M I hI
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient M J
  let q := TauCeti.CommHopfAlgCat.quotientPointsHom M.obj J (CommAlgCat.of k k)
  have huQ : ∀ x : WithConv (Q →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint x := by
    intro x
    have hinj := TauCeti.CommHopfAlgCat.quotientPointsHom_injective M.obj J (CommAlgCat.of k k)
    apply (TauCeti.HopfAlgebra.Point.isUnipotentPoint_iff_semisimplePart_eq_one k Q k x).mpr
    apply hinj
    calc q (TauCeti.HopfAlgebra.Point.semisimplePart k Q k x) =
          TauCeti.HopfAlgebra.Point.semisimplePart k M k (q x) :=
        (TauCeti.HopfAlgebra.Point.semisimplePart_mapDomain
          (TauCeti.CommHopfAlgCat.mkQuotient M.obj J).hom x).symm
      _ = 1 := (TauCeti.HopfAlgebra.Point.isUnipotentPoint_iff_semisimplePart_eq_one
        k M k (q x)).mp (hu (q x) (hJI (Set.mem_range_self x)))
      _ = q 1 := (map_one (TauCeti.AlgHom.mapDomain (A := k)
        (TauCeti.CommHopfAlgCat.mkQuotient M.obj J).hom)).symm
  have hJaug := eq_augmentation_of_reductive_normal_unipotent M hM J hJn hJconn hJred huQ
  let W := TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k)
  let Y := TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k)
  have hYbot : Y.subgroupOf W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hx' : (x : WithConv (M →ₐ[k] k)) ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj
          (TauCeti.HopfIdeal.augmentation k M) (CommAlgCat.of k k) := hJaug ▸ hx
    exact (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_augmentation_iff _ _ _).mp hx'
  have hfinite : Finite (Y.subgroupOf W) := by
    rw [hYbot]
    infer_instance
  let : Finite W := (Subgroup.finite_iff_finite_and_finiteIndex (Y.subgroupOf W)).mpr
    ⟨hfinite, hJfi⟩
  exact Set.toFinite _

theorem eq_const_of_reductive_normal_unipotent_image
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : I.IsNormal)
    (hu : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
      TauCeti.HopfAlgebra.IsUnipotentPoint x)
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [IsReduced A] [ConnectedSpace (PrimeSpectrum A)]
    (f : M →ₐ[k] A) (p₀ : A →ₐ[k] k)
    (hp₀ : toConv (p₀.comp f) = (1 : WithConv (M →ₐ[k] k)))
    (hf : ∀ p : A →ₐ[k] k, toConv (p.comp f) ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k)) :
    f = (Algebra.ofId k A).comp (Bialgebra.counitAlgHom k M) := by
  have hfin := finite_quotientPointsSubgroup_of_reductive_normal_unipotent M hM I hI hu
  apply AlgHom.ext
  intro a
  have hfinite : (Set.range fun p : A →ₐ[k] k => p (f a)).Finite := by
    apply (hfin.image (fun x : WithConv (M →ₐ[k] k) => x.ofConv a)).subset
    rintro _ ⟨p, rfl⟩
    exact ⟨toConv (p.comp f), hf p, rfl⟩
  have hscalar := TauCeti.eq_algebraMap_of_finite_range_eval (f a) hfinite p₀
  have hidentity : p₀ (f a) = Bialgebra.counitAlgHom k M a := by
    have h := AlgHom.congr_fun (congrArg WithConv.ofConv hp₀) a
    simpa [AlgHom.comp_apply, AlgHom.convOne_apply] using h
  rw [hscalar, hidentity]
  rfl

theorem pointsHom_commute_of_mem_normal_unipotent
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (μ : M →ₐc[k] LaurentPolynomial k)
    (I : TauCeti.HopfIdeal k M) (hI : I.IsNormal)
    (hu : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
      TauCeti.HopfAlgebra.IsUnipotentPoint x)
    (hcomm : ∀ t : kˣ, ∀ g : WithConv (M →ₐ[k] k),
      TauCeti.Cocharacter.pointsHom k μ t * g *
        (TauCeti.Cocharacter.pointsHom k μ t)⁻¹ * g⁻¹ ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k)) :
    ∀ t : kˣ, ∀ g : WithConv (M →ₐ[k] k),
      Commute (TauCeti.Cocharacter.pointsHom k μ t) g := by
  intro t g
  let z : WithConv (M →ₐ[k] LaurentPolynomial k) := toConv μ.toAlgHom
  let c : WithConv (M →ₐ[k] LaurentPolynomial k) :=
    TauCeti.AlgHom.mapValue (Algebra.ofId k (LaurentPolynomial k)) g
  let δ : WithConv (M →ₐ[k] LaurentPolynomial k) := z * c * z⁻¹ * c⁻¹
  have heval (p : LaurentPolynomial k →ₐ[k] k) :
      toConv (p.comp δ.ofConv) =
        TauCeti.Cocharacter.pointsHom k μ (TauCeti.MultiplicativeGroup.unitOfPoint p) * g *
          (TauCeti.Cocharacter.pointsHom k μ (TauCeti.MultiplicativeGroup.unitOfPoint p))⁻¹ * g⁻¹ := by
    have hz : TauCeti.AlgHom.mapValue p z =
        TauCeti.Cocharacter.pointsHom k μ (TauCeti.MultiplicativeGroup.unitOfPoint p) := by
      rw [TauCeti.Cocharacter.pointsHom_apply, TauCeti.MultiplicativeGroup.point_unitOfPoint]
      rw [TauCeti.AlgHom.mapValue_apply, TauCeti.AlgHom.mapDomain_apply]
    have hc : TauCeti.AlgHom.mapValue p c = g := by
      apply WithConv.ofConv_injective
      ext a
      simp only [c, TauCeti.AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply]
      exact (p.commutes (g.ofConv a)).trans (by simp)
    rw [← TauCeti.AlgHom.mapValue_apply]
    simp only [δ, map_mul, map_inv, hz, hc]
  let p₀ := TauCeti.MultiplicativeGroup.point (R := k) (1 : kˣ)
  have hp₀ : toConv (p₀.comp δ.ofConv) = (1 : WithConv (M →ₐ[k] k)) := by
    rw [heval]
    have hu0 : TauCeti.MultiplicativeGroup.unitOfPoint p₀ = (1 : kˣ) := by
      apply Units.ext
      simp [p₀]
    rw [hu0, map_one]
    simp
  have hd := eq_const_of_reductive_normal_unipotent_image M hM I hI hu
    (LaurentPolynomial k) δ.ofConv p₀ hp₀ (fun p => by rw [heval]; exact hcomm _ g)
  have hδ1 : toConv ((TauCeti.MultiplicativeGroup.point (R := k) t).comp δ.ofConv) =
      (1 : WithConv (M →ₐ[k] k)) := by
    apply WithConv.ofConv_injective
    ext a
    change TauCeti.MultiplicativeGroup.point (R := k) t (δ.ofConv a) = _
    rw [hd]
    simp [AlgHom.convOne_apply]
  have hu_t : TauCeti.MultiplicativeGroup.unitOfPoint
      (TauCeti.MultiplicativeGroup.point (R := k) t) = t := by
    apply Units.ext
    simp
  rw [heval, hu_t] at hδ1
  rw [commute_iff_eq]
  have h := mul_inv_eq_one.mp hδ1
  exact mul_inv_eq_iff_eq_mul.mp h

end CFSG.LieType.AlgebraicGroups.CanonicalReductive
