module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridge
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
public import CFSG.Sporadic.Schreier.Outer

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise

theorem card_outer_le_six {T : Type} [Group T] (h : StatedClassicalModel T .POmegaPlus 4 2 1) :
    Nat.card (Outer T) ≤ 6 := by
  have h0 := h
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
    (.inr (.inl rfl)) 4 2 1 h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
    (.inr (.inl rfl)) 4 2 1 h) K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit h hK e
  have hout : Nat.card (Outer T) =
      Nat.card (Outer (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (coordinatePlusWitnessEquiv K e)).toEquiv
  have hQ := exists_nonzero_value _ (coordinate_model_intrinsic_plus h K hK e).1
  have hidx : (matrixProjectiveImage (coordinateQuadPlus 4 K)).index ≤ 3 := by
    have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
        (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
          (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
      MulAction.index_stabilizer _ _
    rw [← hEA, hst]
    exact (horbit.2.2.2.2.2 rfl).2
  have ha := relIndex_inner_dvd (coordinateQuadPlus 4 K)
  have hA : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 2 := by
    rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hb := relIndex_isometryRange_dvd (coordinateQuadPlus 4 K) hQ
  have hunits : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, hK]
    rfl
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = 1 := by
    rw [IsCyclic.index_powMonoidHom_range, hunits]
    norm_num
  have hc := (relIndex_linearRange_dvd (coordinateQuadPlus 4 K)).trans
    ((Subgroup.card_subgroup_dvd_card (fieldProjection (coordinateQuadPlus 4 K)).range).trans
      (card_ringAut_and_isCyclic hp K hK).1.dvd)
  have hc' : (linearConjugationHom (coordinateQuadPlus 4 K)).range.relIndex
      (matrixProjectiveImage (coordinateQuadPlus 4 K)) = 1 := Nat.dvd_one.1 hc
  rw [hout, card_outer_eq]
  rw [hsq, Nat.dvd_one] at hb
  rw [hb, hc', mul_one, mul_one]
  have ha2 := (Nat.le_of_dvd (Nat.pos_of_ne_zero (by
    have := Nat.card_pos (α := Abelianization (matrixIsometries (coordinateQuadPlus 4 K)))
    omega)) ha).trans hA
  calc _ ≤ 2 * 3 := Nat.mul_le_mul ha2 hidx
    _ = 6 := by norm_num

theorem card_mulAut_le_six {T : Type} [Group T] [Finite T]
    (h : StatedClassicalModel T .POmegaPlus 4 2 1) : Nat.card (MulAut T) ≤ 6 * Nat.card T := by
  rw [(inner T).card_eq_card_quotient_mul_card_subgroup]
  refine Nat.mul_le_mul (card_outer_le_six h) ?_
  exact Nat.card_le_card_of_surjective _ (MulAut.conj : T →* MulAut T).rangeRestrict_surjective

@[expose] def F2 : Type := ZMod 2

instance : Field F2 := inferInstanceAs (Field (ZMod 2))

instance : Finite F2 := inferInstanceAs (Finite (ZMod 2))

theorem card_F2 : Nat.card F2 = 2 := by
  change Nat.card (ZMod 2) = 2
  simp

instance : CharP F2 2 := charP_two_of_card_eq_two card_F2

@[expose] def omegaElementaryEquiv
    : omegaT ≃* orthElementaryGroup (quadPlus 4 F2) :=
  omegaRestrictEquiv.trans (elementaryOmega1Equiv card_F2).symm

theorem statedClassicalModel_omegaT
    : StatedClassicalModel omegaT .POmegaPlus 4 2 1 :=
  ⟨⟨Nat.prime_two, le_rfl, le_rfl⟩, F2, inferInstance, inferInstance,
    by rw [card_F2]; rfl,
    ⟨omegaElementaryEquiv.trans (OrthogonalSplit.statedProjOmegaPlusEquiv (by norm_num)).symm⟩⟩

theorem lieModel_omegaT
    : CFSG.Blueprint.LieModel omegaT .POmegaPlus 4 2 1 :=
  Or.inl ⟨by decide, statedClassicalModel_omegaT⟩

theorem finite_mulAut_omegaT : Finite (MulAut omegaT) :=
  Finite.of_injective (fun α : MulAut omegaT => (α : omegaT → omegaT)) DFunLike.coe_injective

theorem autConj_bijective : Function.Bijective autConj := by
  have := finite_mulAut_omegaT
  refine autConj_injective.bijective_of_nat_card_le ?_
  calc Nat.card (MulAut omegaT) ≤ 6 * Nat.card omegaT :=
        card_mulAut_le_six statedClassicalModel_omegaT
    _ = Nat.card autT := card_autT_eq.symm

@[expose] def autEquiv
    : autT ≃* MulAut omegaT := MulEquiv.ofBijective autConj autConj_bijective

theorem autEquiv_apply (a : autT) (g : omegaT) :
    ((autEquiv a g : omegaT) : Equiv.Perm (Fin 360)) = a * g * (a : Equiv.Perm (Fin 360))⁻¹ :=
  rfl

theorem card_mulAut_omegaT
    : Nat.card (MulAut omegaT) = 1045094400 := by
  rw [← Nat.card_congr autEquiv.toEquiv, card_autT]

theorem center_omegaT : Subgroup.center omegaT = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hc : (z : Equiv.Perm (Fin 360)) ∈
      Subgroup.centralizer (omegaT : Set (Equiv.Perm (Fin 360))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨h, hh⟩)
  rw [centralizer_omegaT, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.2 (Subtype.ext hc)

theorem card_outer_omegaT : Nat.card (Outer omegaT) = 6 := by
  have h := (CFSG.ComponentClassification.OuterAutomorphisms.inner
    omegaT).card_eq_card_quotient_mul_card_subgroup
  rw [CFSG.Sporadic.Schreier.card_inner_of_center_eq_bot center_omegaT, card_mulAut_omegaT,
    card_omegaT] at h
  change Nat.card (MulAut omegaT ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner omegaT) = 6
  omega

end CFSG.EvenSmallLie.OmegaEight
