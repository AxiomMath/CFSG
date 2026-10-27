module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataWitnessOuterOrbitBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataWitnessOuterModels

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CatalogueBOrthogonalSmallFamilyOrbit CatalogueBStabilizerFamily
open CatalogueBOrthogonalPointAction (Points)
open scoped Pointwise

variable {G : Type} [Group G] {n p f : ℕ}

section Witness

variable (K : Type) [Field K]

@[expose] def plusWitnessAction (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    G →* Equiv.Perm (Points (CatalogueBOrthogonalPointData.coordinateQuadPlus n K)) :=
  (CatalogueBOrthogonalPointData.projectivePointAction
    (CatalogueBOrthogonalPointData.coordinateQuadPlus n K)).comp
    (CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K e).toMonoidHom

theorem plusWitness_family_transport (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    familyTransport (CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K e)
        (family (plusWitnessAction K e)) =
      CatalogueBOrthogonalPointData.projectivePointFamily
        (CatalogueBOrthogonalPointData.coordinateQuadPlus n K) :=
  pointFamily_comp_equiv_transport _ _

theorem plusWitness_family_fixed (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    (alpha : MulAut G)
    (h : MulAut.congr (CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K e) alpha •
        CatalogueBOrthogonalPointData.projectivePointFamily
          (CatalogueBOrthogonalPointData.coordinateQuadPlus n K) =
      CatalogueBOrthogonalPointData.projectivePointFamily
        (CatalogueBOrthogonalPointData.coordinateQuadPlus n K)) :
    alpha • family (plusWitnessAction K e) = family (plusWitnessAction K e) := by
  apply (familyTransport (CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K e)).injective
  rw [familyTransport_automorphism, plusWitness_family_transport]
  exact h

end Witness

theorem orthogonal_geometry_plus_classical_model_Schreier
    (h : StatedClassicalModel G .POmegaPlus n p f) :
    (5 ≤ n → derivedSeries (OuterAutomorphisms.Outer G) 3 = ⊥) ∧
    (n = 4 → derivedSeries (OuterAutomorphisms.Outer G) 5 = ⊥) ∧
    Group.IsSolvable (OuterAutomorphisms.Outer G) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have hn : 4 ≤ n := h.1.2.2
  have : Finite (StatedProj (StatedOmega (StatedQuadPlus n K))) := inferInstance
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨-, hc, hG⟩ := CatalogueBOrthogonalPointData.coordinate_model_intrinsic_plus h K hK e
  let x : Points (CatalogueBOrthogonalPointData.coordinateQuadPlus n K) :=
    CatalogueBOrthogonalPointReindexCovariance.reindexPointEquiv
      (CatalogueBOrthogonalPointData.plusIndexEquiv n) (quadPlus n K) (firstPoint (by omega))
  have hfamily : family (plusWitnessAction K e) =
      conjugacyFamily (pointStabilizer (plusWitnessAction K e) x) := (hG.2.2 x).1
  have hd := CatalogueBOrthogonalPointData.coordinate_plus_familyOuter_witness_thirdDerived
    h K hK e
  have h5 : 5 ≤ n → derivedSeries (OuterAutomorphisms.Outer G) 3 = ⊥ := by
    intro h5
    refine CatalogueBOrthogonalPointData.outer_derived_eq_bot_of_point_family_top
      (plusWitnessAction K e) x hfamily 3 hd ?_
    refine eq_top_iff.mpr fun alpha _ => ?_
    refine plusWitness_family_fixed K e alpha ?_
    have htop := coordinate_plus_pointFamilyAut_eq_top (K := K) h5
    have hmem : MulAut.congr (CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K e)
        alpha ∈ CatalogueBOrthogonalPointData.projectivePointFamilyAut
          (CatalogueBOrthogonalPointData.coordinateQuadPlus n K) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hmem
  have h4 : n = 4 → derivedSeries (OuterAutomorphisms.Outer G) 5 = ⊥ := by
    intro h4
    refine CatalogueBOrthogonalPointData.outer_derived_eq_bot_of_small_point_family
      (plusWitnessAction K e) x hfamily 3 hd ?_
    rw [familyOrbitTransport_card (CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K e),
      plusWitnessAction, pointStabilizer_comp_equiv_map]
    have horbit := (orthogonal_geometry_plus_point_family_orbit h hK e).2.2.2.2.2 h4
    have hFc : CatalogueBOrthogonalPointData.projectivePointFamily
        (CatalogueBOrthogonalPointData.coordinateQuadPlus n K) =
        conjugacyFamily (pointStabilizer (CatalogueBOrthogonalPointData.projectivePointAction
          (CatalogueBOrthogonalPointData.coordinateQuadPlus n K)) x) := (hc.2.2 x).1
    change Nat.card ↥(MulAction.orbit _ (conjugacyFamily _)) ≤ 3
    rw [Nat.card_coe_set_eq, ← hFc]
    exact horbit.2
  refine ⟨h5, h4, ?_⟩
  rcases Nat.lt_or_ge n 5 with hlt | hge
  · exact ⟨⟨5, h4 (by omega)⟩⟩
  · exact ⟨⟨3, h5 hge⟩⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
