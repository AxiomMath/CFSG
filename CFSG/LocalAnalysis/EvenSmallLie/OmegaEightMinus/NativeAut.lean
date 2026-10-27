module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeBridge
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEightMinus

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail (quadTail minusTailForm minusTailIsometry
  tailProjEquiv)
open CFSG.EvenSmallLie.OmegaEight (F2 card_F2 eq_zero_or_eq_one_of_card_eq_two one_add_one_eq_zero)

theorem card_outer_le_two {T : Type} [Group T] (h : StatedClassicalModel T .POmegaMinus 4 2 1) :
    Nat.card (Outer T) ≤ 2 := by
  have h0 := h
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hn1 : 1 ≤ 4 := by norm_num
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaMinus
    (.inr (.inr rfl)) 4 2 1 h K hK b c hirr (quadMinus 4 K b c) (coe_quadMinus 4 K b c) e
  have hE : matrixProjectiveImage (coordinateQuadMinus 4 K hn1 b c) = ⊤ := by
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaMinus
      (.inr (.inr rfl)) 4 2 1 h) hn1 K hK b c hirr e).1]
    exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T
      .POmegaMinus (.inr rfl) 4 2 1 h) hn1 K hK b c hirr).2
  have hout : Nat.card (Outer T) =
      Nat.card (Outer (matrixProjectiveDerived (coordinateQuadMinus 4 K hn1 b c))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (coordinateMinusWitnessEquiv K hn1 b c e)).toEquiv
  have hQ := exists_nonzero_value _ (coordinate_model_intrinsic_minus h K hK b c hirr e).1
  have ha := relIndex_inner_dvd (coordinateQuadMinus 4 K hn1 b c)
  have hA : Nat.card (Abelianization (matrixIsometries (coordinateQuadMinus 4 K hn1 b c))) ≤ 2 := by
    rw [coordinateQuadMinus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hb := relIndex_isometryRange_dvd (coordinateQuadMinus 4 K hn1 b c) hQ
  have hunits : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, hK]
    rfl
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = 1 := by
    rw [IsCyclic.index_powMonoidHom_range, hunits]
    norm_num
  have hc := (relIndex_linearRange_dvd (coordinateQuadMinus 4 K hn1 b c)).trans
    ((Subgroup.card_subgroup_dvd_card
      (fieldProjection (coordinateQuadMinus 4 K hn1 b c)).range).trans
        (card_ringAut_and_isCyclic hp K hK).1.dvd)
  have hc' : (linearConjugationHom (coordinateQuadMinus 4 K hn1 b c)).range.relIndex
      (matrixProjectiveImage (coordinateQuadMinus 4 K hn1 b c)) = 1 := Nat.dvd_one.1 hc
  rw [hout, card_outer_eq]
  rw [hsq, Nat.dvd_one] at hb
  rw [hb, hc', hE, Subgroup.index_top, mul_one, mul_one, mul_one]
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (by
    have := Nat.card_pos (α := Abelianization (matrixIsometries (coordinateQuadMinus 4 K hn1 b c)))
    omega)) ha).trans hA

theorem card_mulAut_le_two {T : Type} [Group T] [Finite T]
    (h : StatedClassicalModel T .POmegaMinus 4 2 1) : Nat.card (MulAut T) ≤ 2 * Nat.card T := by
  rw [(inner T).card_eq_card_quotient_mul_card_subgroup]
  refine Nat.mul_le_mul (card_outer_le_two h) ?_
  exact Nat.card_le_card_of_surjective _ (MulAut.conj : T →* MulAut T).rangeRestrict_surjective

theorem irr_F2 : ∀ s : F2, s ^ 2 + 1 * s + 1 ≠ 0 := by
  intro s
  rcases eq_zero_or_eq_one_of_card_eq_two card_F2 s with rfl | rfl
  · simp
  · rw [one_pow, one_mul, one_add_one_eq_zero card_F2, zero_add]
    exact one_ne_zero

@[expose] def statedMinusEquiv :
    StatedProj (StatedOmega (StatedQuadMinus 4 F2 1 1)) ≃* orthElementaryGroup (qM F2) :=
  (tailProjEquiv (minusTailIsometry 4 F2 1 1) (coe_quadMinus 4 F2 1 1)
    (commutator_orthogonalGroup_quadMinus (n := 4) (by norm_num) irr_F2)).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (NonsplitOrthogonalCover.elemScalars_quadTail_eq_bot (by norm_num))).trans
      QuotientGroup.quotientBot)

theorem statedClassicalModel_omegaT
    : StatedClassicalModel omegaT .POmegaMinus 4 2 1 :=
  ⟨⟨Nat.prime_two, le_rfl, le_rfl⟩, F2, inferInstance, inferInstance, by rw [card_F2]; rfl, 1, 1,
    irr_F2, ⟨(elementaryOmegaEquiv card_F2).symm.trans statedMinusEquiv.symm⟩⟩

theorem finite_mulAut_omegaT : Finite (MulAut omegaT) :=
  Finite.of_injective (fun α : MulAut omegaT => (α : omegaT → omegaT)) DFunLike.coe_injective

theorem autConj_bijective : Function.Bijective autConj := by
  have := finite_mulAut_omegaT
  refine autConj_injective.bijective_of_nat_card_le ?_
  calc Nat.card (MulAut omegaT) ≤ 2 * Nat.card omegaT :=
        card_mulAut_le_two statedClassicalModel_omegaT
    _ = Nat.card autT := card_autT_eq.symm

@[expose] def autEquiv
    : autT ≃* MulAut omegaT := MulEquiv.ofBijective autConj autConj_bijective

theorem autEquiv_apply (a : autT) (g : omegaT) :
    ((autEquiv a g : omegaT) : Equiv.Perm (Fin 136)) = a * g * (a : Equiv.Perm (Fin 136))⁻¹ :=
  rfl

theorem card_mulAut_omegaT
    : Nat.card (MulAut omegaT) = 394813440 := by
  rw [← Nat.card_congr autEquiv.toEquiv, card_autT]

theorem center_omegaT : Subgroup.center omegaT = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hc : (z : Equiv.Perm (Fin 136)) ∈
      Subgroup.centralizer (omegaT : Set (Equiv.Perm (Fin 136))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨h, hh⟩)
  rw [centralizer_omegaT, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.2 (Subtype.ext hc)

theorem card_outer_omegaT : Nat.card (Outer omegaT) = 2 := by
  have h := (CFSG.ComponentClassification.OuterAutomorphisms.inner
    omegaT).card_eq_card_quotient_mul_card_subgroup
  rw [CFSG.Sporadic.Schreier.card_inner_of_center_eq_bot center_omegaT, card_mulAut_omegaT,
    card_omegaT] at h
  change Nat.card (MulAut omegaT ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner omegaT) = 2
  omega

end CFSG.EvenSmallLie.OmegaEightMinus
