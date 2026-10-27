module

public import CFSG.ThirdParty.TauCeti.CommutativeJordan
public import CFSG.LieType.AlgebraicGroups.DerivedSemisimple
public import TauCeti.Algebra.AlgebraicGroup.Derived.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Derived.Connected
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Derived.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Derived.Series
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Reduced

public noncomputable section

open TauCeti WithConv
open scoped commutatorElement
namespace CFSG.LieType.AlgebraicGroups.NilpotentSemisimple
universe u
variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [_root_.HopfAlgebra k H]

theorem commute_of_unipotent_commutator_centralizes
    (s x : WithConv (H →ₐ[k] k)) (hs : HopfAlgebra.IsSemisimplePoint s)
    (hu : HopfAlgebra.IsUnipotentPoint ⁅s,x⁆) (hc : Commute s ⁅s,x⁆) : Commute s x := by
  have hcx : Commute s (x * s⁻¹ * x⁻¹) := by
    have hx : x * s⁻¹ * x⁻¹ = s⁻¹ * ⁅s,x⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hx]
    exact (Commute.refl s).inv_right.mul_right hc
  have ht : HopfAlgebra.IsSemisimplePoint (x * s⁻¹ * x⁻¹) :=
    (HopfAlgebra.isSemisimplePoint_conj_iff s⁻¹ x).mpr hs.inv
  have hd : HopfAlgebra.IsSemisimplePoint ⁅s,x⁆ := by
    simpa only [commutatorElement_def,mul_assoc] using hs.mul_of_commute ht hcx
  have h1 : ⁅s,x⁆ = 1 := by
    calc ⁅s,x⁆ = HopfAlgebra.Point.semisimplePart k H k ⁅s,x⁆ :=
        (HopfAlgebra.Point.semisimplePart_eq_self k H k
          ((HopfAlgebra.isSemisimplePoint_def _).mp hd)).symm
      _ = 1 := HopfAlgebra.Point.semisimplePart_eq_one_of_isUnipotent k H k hu
  exact commutatorElement_eq_one_iff_commute.mp h1

theorem commute_of_mem_upperCentralSeries
    (s : WithConv (H →ₐ[k] k)) (hs : HopfAlgebra.IsSemisimplePoint s)
    (hu : ∀ x : WithConv (H →ₐ[k] k), HopfAlgebra.IsUnipotentPoint ⁅s,x⁆)
    (n : ℕ) {x : WithConv (H →ₐ[k] k)}
    (hx : x ∈ Subgroup.upperCentralSeries (WithConv (H →ₐ[k] k)) n) : Commute s x := by
  induction n generalizing x with
  | zero =>
    have hx1 : x = 1 := by simpa using hx
    rw [hx1]
    exact Commute.one_right s
  | succ n ih =>
    have hxs : ⁅x,s⁆ ∈ Subgroup.upperCentralSeries (WithConv (H →ₐ[k] k)) n :=
      (Subgroup.mem_upperCentralSeries_succ_iff.mp hx) s
    have hsx : ⁅s,x⁆ ∈ Subgroup.upperCentralSeries (WithConv (H →ₐ[k] k)) n := by
      simpa only [commutatorElement_inv] using
        (Subgroup.upperCentralSeries (WithConv (H →ₐ[k] k)) n).inv_mem hxs
    exact commute_of_unipotent_commutator_centralizes s x hs (hu x) (ih hsx)

theorem isCentral_semisimple_of_nilpotent
    [Group.IsNilpotent (WithConv (H →ₐ[k] k))]
    (s : WithConv (H →ₐ[k] k)) (hs : HopfAlgebra.IsSemisimplePoint s)
    (hu : ∀ x : WithConv (H →ₐ[k] k), HopfAlgebra.IsUnipotentPoint ⁅s,x⁆) :
    ∀ x : WithConv (H →ₐ[k] k), Commute s x := by
  obtain ⟨n, hn⟩ := Group.IsNilpotent.nilpotent (WithConv (H →ₐ[k] k))
  intro x
  exact commute_of_mem_upperCentralSeries s hs hu n (hn ▸ Subgroup.mem_top x)
theorem isUnipotentPoint_commutator_of_solvable
    (G : FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced G]
    (hc : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsol : geometricallySolvablePointsCommHopfAlgProperty k G.obj)
    (g h : WithConv (G →ₐ[k] k)) : HopfAlgebra.IsUnipotentPoint ⁅g,h⁆ := by
  let : ConnectedSpace (PrimeSpectrum G) := hc.connectedSpace k G.obj
  let I := TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) G
  have hconn : geometricallyConnectedCommHopfAlgProperty k
      (TauCeti.CommHopfAlgCat.quotient G.obj I) :=
    TauCeti.CommHopfAlgCat.geometricallyConnectedCommHopfAlgProperty_derived G
  have hsm : Algebra.Smooth k (G ⧸ I.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (TauCeti.CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_derivedDefiningIdeal G.obj)
  have hsolD : geometricallySolvablePointsCommHopfAlgProperty k
      (TauCeti.CommHopfAlgCat.quotient G.obj I) :=
    (geometricallySolvablePointsCommHopfAlgProperty_iff_derived k G.obj).mp hsol
  have hU := DerivedSemisimple.smoothUnipotent_of_le_derived G I
    (TauCeti.CommHopfAlgCat.isNormal_derivedDefiningIdeal G.obj) le_rfl hconn hsm hsolD
  obtain ⟨y, hy⟩ := TauCeti.CommHopfAlgCat.commutator_mem_derivedPointsSubgroup G.obj
    (CommAlgCat.of k k) g h
  rw [← hy]
  exact (((smoothUnipotentCommHopfAlgProperty.iff_smooth_and_forall_isUnipotentPoint k).mp hU).2 y).mapDomain
    (TauCeti.CommHopfAlgCat.mkQuotient G.obj I).hom

theorem commute_semisimplePoint_of_nilpotent
    (G : FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced G]
    (hc : geometricallyConnectedCommHopfAlgProperty k G.obj)
    [Group.IsNilpotent (WithConv (G →ₐ[k] k))]
    (s : WithConv (G →ₐ[k] k)) (hs : HopfAlgebra.IsSemisimplePoint s) :
    ∀ x : WithConv (G →ₐ[k] k), Commute s x := by
  have hsol : geometricallySolvablePointsCommHopfAlgProperty k G.obj := by
    apply (geometricallySolvablePointsCommHopfAlgProperty.iff_exists_derivedSeriesDefiningIdeal_eq_augmentation
      G.obj).mpr
    exact G.obj.isSolvable_points_iff_exists_derivedSeriesDefiningIdeal_eq_augmentation.mp inferInstance
  exact isCentral_semisimple_of_nilpotent s hs
    (isUnipotentPoint_commutator_of_solvable G hc hsol s)

private theorem central_semisimpleParts
    (G : FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced G]
    (hc : geometricallyConnectedCommHopfAlgProperty k G.obj)
    [Group.IsNilpotent (WithConv (G →ₐ[k] k))] :
    ∀ g x : WithConv (G →ₐ[k] k), Commute (HopfAlgebra.Point.semisimplePart k G k g) x := by
  intro g x
  exact commute_semisimplePoint_of_nilpotent G hc _
    ((HopfAlgebra.isSemisimplePoint_def _).mpr
      (HopfAlgebra.Point.isSemisimple_pointsAction_semisimplePart k G k g)) x

theorem exists_unique_isMaximalTorus_of_nilpotent
    (G : FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced G]
    (hc : geometricallyConnectedCommHopfAlgProperty k G.obj)
    [Group.IsNilpotent (WithConv (G →ₐ[k] k))] :
    ∃! J : HopfIdeal k G, HopfIdeal.IsMaximalTorus k G.obj J := by
  let : ConnectedSpace (PrimeSpectrum G) := hc.connectedSpace k G.obj
  have hcentral := central_semisimpleParts G hc
  let hreg := CFSG.ThirdParty.TauCeti.CentralJordan.exists_mem_groupLikeSetSpan_forall_apply_eq hcentral
  let hmul := CFSG.ThirdParty.TauCeti.CentralJordan.semisimplePart_mul_of_central_parts hcentral
  refine ⟨_, CFSG.ThirdParty.TauCeti.RegularJordan.isMaximalTorus_semisimpleImage hreg hmul hc,
    fun J hJ ↦ ?_⟩
  exact (CFSG.ThirdParty.TauCeti.RegularJordan.isMaximalTorus_iff_eq_ker_semisimplePartBialgHom
    hreg hmul hc J).mp hJ

end CFSG.LieType.AlgebraicGroups.NilpotentSemisimple
