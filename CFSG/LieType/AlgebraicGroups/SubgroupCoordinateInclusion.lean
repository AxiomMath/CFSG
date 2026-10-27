module
public import CFSG.LieType.AlgebraicGroups.TorusPointSubgroups
public import CFSG.LieType.AlgebraicGroups.G2ExceptionalComorphism
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open WithConv Subgroup CategoryTheory
open scoped CFSG.ConvolutionPoints

variable {k : Type} [Field k] [IsAlgClosed k]
 {A : Type} [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A]

def subgroupCoordinateInclusion
    {T K : Subgroup (WithConv (A →ₐ[k] k))} (hTK : T ≤ K) :
    (A ⧸ subgroupIdeal K) →ₐc[k] (A ⧸ subgroupIdeal T) := by
  have hI : subgroupIdeal K ≤ subgroupIdeal T := fun a ha => mem_subgroupIdeal.mpr
    (fun y hy => mem_subgroupIdeal.mp ha y (hTK hy))
  exact Bialgebra.Quotient.liftBialgHom (subgroupIdeal K)
    (Bialgebra.Quotient.mkBialgHom (subgroupIdeal T))
    (by intro a ha; change Ideal.Quotient.mk (subgroupIdeal T) a = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI ha))

theorem subgroupCoordinateInclusion_mk
    {T K : Subgroup (WithConv (A →ₐ[k] k))} (hTK : T ≤ K) (a : A) :
    subgroupCoordinateInclusion hTK (Ideal.Quotient.mk (subgroupIdeal K) a) =
      Ideal.Quotient.mk (subgroupIdeal T) a := by
  dsimp only [subgroupCoordinateInclusion]
  rw [Bialgebra.Quotient.liftBialgHom_mk, Bialgebra.Quotient.mkBialgHom_apply]

theorem subgroupCoordinateInclusion_surjective
    {T K : Subgroup (WithConv (A →ₐ[k] k))} (hTK : T ≤ K) :
    Function.Surjective (subgroupCoordinateInclusion hTK) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk (subgroupIdeal K) a,
    subgroupCoordinateInclusion_mk hTK a⟩

noncomputable def subgroupHopfIdeal
    {T K : Subgroup (WithConv (A →ₐ[k] k))} (hTK : T ≤ K) :
    TauCeti.HopfIdeal k (A ⧸ subgroupIdeal K) :=
  TauCeti.HopfIdeal.kerOfSurjective (subgroupCoordinateInclusion hTK)
    (subgroupCoordinateInclusion_surjective hTK)

noncomputable def subgroupCoordinateIso
    {T K : Subgroup (WithConv (A →ₐ[k] k))} (hTK : T ≤ K) :
    TauCeti.FiniteTypeCommHopfAlgCat.quotient
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal K))
      (subgroupHopfIdeal hTK) ≅
        TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal T) :=
  ObjectProperty.isoMk _ (TauCeti.CommHopfAlgCat.quotientKerOfSurjectiveIso
    (CommHopfAlgCat.ofHom (subgroupCoordinateInclusion hTK))
    (subgroupCoordinateInclusion_surjective hTK))

theorem torus_subgroupHopfIdeal
    {T K : Subgroup (WithConv (A →ₐ[k] k))} (hTK : T ≤ K)
    (hT : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal T))) :
    TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal K))
        (subgroupHopfIdeal hTK)) :=
  (TauCeti.torusCommHopfAlgProperty k).prop_of_iso (subgroupCoordinateIso hTK).symm hT

theorem mem_subgroupHopfIdeal_mk
    {T K : Subgroup (WithConv (A →ₐ[k] k))} (hTK : T ≤ K) (a : A) :
    Ideal.Quotient.mk (subgroupIdeal K) a ∈ subgroupHopfIdeal hTK ↔
      a ∈ subgroupIdeal T := by
  rw [← TauCeti.HopfIdeal.mem_toIdeal, subgroupHopfIdeal,
    TauCeti.HopfIdeal.kerOfSurjective_toIdeal, RingHom.mem_ker]
  change subgroupCoordinateInclusion hTK (Ideal.Quotient.mk (subgroupIdeal K) a) = 0 ↔ _
  rw [subgroupCoordinateInclusion_mk, Ideal.Quotient.eq_zero_iff_mem]

theorem quotientPoints_subgroupHopfIdeal_eq
    {T K : Subgroup (WithConv (A →ₐ[k] k))} (hTK : T ≤ K)
    (hT : pointsZero k (subgroupIdeal T) = subgroupPoints T)
    (hK : pointsZero k (subgroupIdeal K) = subgroupPoints K) :
    let e := subgroupQuotientPointsEquiv K hK
    (ofTauCeti (TauCeti.CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of k (A ⧸ subgroupIdeal K)) (subgroupHopfIdeal hTK)
        (CommAlgCat.of k k))).map e.toMonoidHom = T.subgroupOf K := by
  let e := subgroupQuotientPointsEquiv K hK
  ext x
  rw [Subgroup.mem_map_equiv]
  change e.symm x ∈ ofTauCeti (TauCeti.CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of k (A ⧸ subgroupIdeal K)) (subgroupHopfIdeal hTK)
        (CommAlgCat.of k k)) ↔ (x : WithConv (A →ₐ[k] k)) ∈ T
  rw [mem_ofTauCeti, TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  constructor
  · intro hx
    have hvan : x.val.ofConv ∈ pointsZero k (subgroupIdeal T) := by
      intro a ha
      have h := hx (Ideal.Quotient.mk (subgroupIdeal K) a)
        ((mem_subgroupHopfIdeal_mk hTK a).mpr ha)
      have hcomp := subgroupQuotientPointsEquiv_apply K hK (e.symm x)
      have ha' := DFunLike.congr_fun hcomp a
      rw [e.apply_symm_apply] at ha'
      exact ha'.trans h
    rwa [hT] at hvan
  · intro hx q hq
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    have ha := (mem_subgroupHopfIdeal_mk hTK a).mp hq
    have h := mem_subgroupIdeal.mp ha x.val hx
    have hcomp := subgroupQuotientPointsEquiv_apply K hK (e.symm x)
    have ha' := DFunLike.congr_fun hcomp a
    rw [e.apply_symm_apply] at ha'
    exact ha'.symm.trans h

theorem subgroupHopfIdeal_isMaximalTorus_of_point_maximal
    {T K : Subgroup (WithConv (A →ₐ[k] k))} (hTK : T ≤ K)
    (hT : pointsZero k (subgroupIdeal T) = subgroupPoints T)
    (hK : pointsZero k (subgroupIdeal K) = subgroupPoints K)
    (htor : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal T)))
    (hmax : ∀ J : TauCeti.HopfIdeal k (A ⧸ subgroupIdeal K),
      TauCeti.torusCommHopfAlgProperty k
        (TauCeti.FiniteTypeCommHopfAlgCat.of k ((A ⧸ subgroupIdeal K) ⧸ J.toIdeal)) →
      J ≤ subgroupHopfIdeal hTK →
      ∀ x : WithConv ((A ⧸ subgroupIdeal K) →ₐ[k] k),
        x ∈ ofTauCeti (TauCeti.CommHopfAlgCat.quotientPointsSubgroup
          (CommHopfAlgCat.of k (A ⧸ subgroupIdeal K)) J (CommAlgCat.of k k)) →
        ((subgroupQuotientPointsEquiv K hK x : K) : WithConv (A →ₐ[k] k)) ∈ T) :
    TauCeti.HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k (A ⧸ subgroupIdeal K))
      (subgroupHopfIdeal hTK) := by
  let I := subgroupHopfIdeal hTK
  have hI := torus_subgroupHopfIdeal hTK htor
  have hI' : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k ((A ⧸ subgroupIdeal K) ⧸ I.toIdeal)) := hI
  rw [TauCeti.HopfIdeal.isMaximalTorus_iff]
  refine ⟨hI', ?_⟩
  intro J hJ hJI
  have : IsReduced ((A ⧸ subgroupIdeal K) ⧸ I.toIdeal) := hI'.geometricallyReduced.isReduced
  have : IsReduced ((A ⧸ subgroupIdeal K) ⧸ J.toIdeal) := hJ.geometricallyReduced.isReduced
  apply le_of_eq
  change I = J
  apply TauCeti.HopfIdeal.eq_of_quotientPointsSubgroup_eq (k := k) (K := k)
    (H := CommHopfAlgCat.of k (A ⧸ subgroupIdeal K)) (I := I) (J := J)
  apply le_antisymm (TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_of_le _ hJI (CommAlgCat.of k k))
  intro x hx
  have hxT := hmax J hJ hJI x (mem_ofTauCeti.mpr hx)
  let e := subgroupQuotientPointsEquiv K hK
  have hmap := quotientPoints_subgroupHopfIdeal_eq hTK hT hK
  have hmem : e x ∈ (ofTauCeti (TauCeti.CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of k (A ⧸ subgroupIdeal K)) I (CommAlgCat.of k k))).map e.toMonoidHom := by
    rw [hmap]
    exact hxT
  have he := Subgroup.mem_map_equiv.mp hmem
  exact mem_ofTauCeti.mp (by simpa using he)

end CFSG.LieType.AlgebraicGroups
