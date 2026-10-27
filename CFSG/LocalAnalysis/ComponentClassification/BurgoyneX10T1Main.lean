module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Iso
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Desc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Main

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

set_option maxHeartbeats 800000 in
theorem twE6TwentyP_model :
    TwE6TwentyP CompPred.model := by
  intro p _ k _ _ _ D hχ hθ J' hq
  have hp : p.Prime := Fact.out
  have he : 1 ≤ D.e := D.one_le_e
  have hΔ : simpleUnion (D.withOrbit J').χ = Set.range e6D5TwRoot := by
    change simpleUnion D.χ = _
    rw [hχ]
    exact simpleUnion_e6_twenty
  rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hΔ (fun i => e6_simple_inter_twenty hχ i)
    with h0 | hJS
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  have hθ2 : ∀ β ∈ (D.withOrbit J').simpleRootsJ,
      (D.withOrbit J').θ ((D.withOrbit J').θ (toReal β)) = toReal β := by
    intro β _
    change D.θ (D.θ (toReal β)) = toReal β
    rw [hθ β, hθ, thetaMap_e6_twice]
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  have hθp : ThetaProperties TwistTag.E6.perm 2 (D.withOrbit J').χ
      (ToralSign.wordElt .E6 []) := by
    change ThetaProperties TwistTag.E6.perm 2 D.χ _
    rw [hχ]
    exact h6.theta ⟨20, 27, 1, e6OmegaWords20⟩ (by simp [e6SignDiagramReps]) []
      (by simp [e6OmegaWords20])
  have hcard : ∀ O ∈ (D.withOrbit J').orbits, orbitCard O = 1 ∨ orbitCard O = 2 := fun O hO =>
    ClassicalInvolution.ModelFacts.orbitCard_eq_of_thetaProperties (D.withOrbit J') hθp hθ hO
  refine CompPred.model.orbitGroup_of_quadGroup_at (D.withOrbit J') hθ2 hcard hq fun L hL => ?_
  have hK₂ : Nat.card (frobeniusFixedField k p (D.e * 2)) = p ^ (D.e * 2) :=
    card_frobeniusFixedField (by omega)
  have : Finite (frobeniusFixedField k p (D.e * 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hK₂]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨eY₀, heY₀⟩ := exists_quadGroup_equiv_pairSpan (D.withOrbit J') hJS
  let eY : quadGroup (D.withOrbit J') ≃*
      pairSpan .E6 (frobeniusFixedField k p (D.e * 2)) (Set.range e6D5TwRoot) := eY₀
  have heY : ∀ y, baseChangeGL (frobeniusFixedField k p (D.e * 2)).subtype
      ((eY y : pairSpan .E6 (frobeniusFixedField k p (D.e * 2)) (Set.range e6D5TwRoot)) :
        ModGL .E6 (frobeniusFixedField k p (D.e * 2))) =
      ((y : adjointGroup .E6 k) : ModGL .E6 k) := heY₀
  obtain ⟨θ, hθs, hθk, N, r, hN2, hN0, hr, hR1, hR2⟩ := exists_pairSpan_e6D5Tw_proj hp D.odd hK₂
  let Φ : ↥(quadGroup (D.withOrbit J')) ⧸ Subgroup.center ↥(quadGroup (D.withOrbit J')) ≃*
      matrixProjectiveDerived (coordinateQuadPlus 5 (frobeniusFixedField k p (D.e * 2))) :=
    (QuotientGroup.congr _ _ eY (Subgroup.map_center_eq eY)).trans
      ((QuotientGroup.quotientMulEquivOfEq hθk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ hθs))
  have hΦ : ∀ y : quadGroup (D.withOrbit J'),
      Φ (y : ↥(quadGroup (D.withOrbit J')) ⧸ Subgroup.center ↥(quadGroup (D.withOrbit J'))) =
        θ (eY y) := fun y => rfl
  have hα₄ : e6D5TwRoot 0 ∈ (D.withOrbit J').simpleRootsJ := hJS ▸ e6D5TwRoot_zero_mem
  have hr4 : IsRoot .E6 (e6D5TwRoot 0) := isRoot_single _ _
  let y : frobeniusFixedField k p (D.e * 2) → quadGroup (D.withOrbit J') := fun c =>
    ⟨⟨rootSL2 .E6 k (e6D5TwRoot 0) (uSL (c : k)), rootSL2_mem_adjointGroup hr4 _⟩,
      Subgroup.subset_closure ⟨_, hα₄, (c : k), c.2, Or.inl rfl⟩⟩
  have heYy : ∀ c, eY (y c) = ⟨rootSL2 .E6 _ (e6D5TwRoot 0) (uSL c),
      rootSL2_uSL_mem_pairSpan e6D5TwRoot_zero_mem c⟩ := by
    intro c
    apply Subtype.ext
    apply baseChangeGL_injective (frobeniusFixedField k p (D.e * 2)).subtype
    rw [heY, baseChangeGL_rootSL2_of_field, CFSG.LieType.Chevalley.map_uSL]
    rfl
  have hθα₄ : (D.withOrbit J').θ (toReal (e6D5TwRoot 0)) = toReal (e6D5TwRoot 0) := by
    change D.θ _ = _
    rw [hθ]
    exact congrArg toReal thetaMap_e6_alpha4
  have hσy : ∀ c, quadAut (D.withOrbit J') hθ2 (y c) = y (c ^ p ^ D.e) := by
    intro c
    apply Subtype.ext
    apply Subtype.ext
    have h := (D.withOrbit J').map_rootSL2 _ hα₄.1 _ hθα₄ (uSL (c : k)) (y c).1 rfl
    change ((D.withOrbit J').F (y c).1 : ModGL .E6 k) = _
    rw [h, CFSG.LieType.Chevalley.map_uSL]
    change rootSL2 .E6 k _ (uSL (iterateFrobenius k p D.e (c : k))) =
      rootSL2 .E6 k _ (uSL ((c ^ p ^ D.e : frobeniusFixedField k p (D.e * 2)) : k))
    rw [iterateFrobenius_def, SubmonoidClass.coe_pow]
  set α := MulAut.congr Φ (quadAutBar (D.withOrbit J') hθ2) with hα
  set w : frobeniusFixedField k p (D.e * 2) →
      matrixProjectiveDerived (coordinateQuadPlus 5 (frobeniusFixedField k p (D.e * 2))) :=
    fun c => θ ⟨rootSL2 .E6 _ (e6D5TwRoot 0) (uSL c),
      rootSL2_uSL_mem_pairSpan e6D5TwRoot_zero_mem c⟩ with hw
  have hwy : ∀ c, w c = Φ (y c : ↥(quadGroup (D.withOrbit J')) ⧸
      Subgroup.center ↥(quadGroup (D.withOrbit J'))) := fun c => by
    rw [hΦ, heYy]
  have hact : ∀ c, α (w c) = w (c ^ p ^ D.e) := by
    intro c
    rw [hwy, hwy, hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, quadAutBar_mk, hσy]
  have hα2 : α ^ 2 = 1 := by
    rw [hα, ← map_pow, quadAutBar_sq, map_one]
  have hfix := card_pow_fixed_frobeniusFixedField (k := k) (p := p) he
  have h1 : Nat.card {c : frobeniusFixedField k p (D.e * 2) // c ^ p ^ D.e = c} ≠ 1 := by
    rw [hfix]
    exact (Nat.one_lt_pow (by omega) hp.one_lt).ne'
  have hKc : Nat.card {c : frobeniusFixedField k p (D.e * 2) // c ^ p ^ D.e = c} ≠
      Nat.card (frobeniusFixedField k p (D.e * 2)) := by
    rw [hfix, hK₂]
    intro h
    have := Nat.pow_right_injective hp.two_le h
    omega
  refine CompPred.model.of_component_equiv (fixedSubgroupCongrEquiv Φ _) (fun M hM => ?_) hL
  exact excCompModel_of_root_fixed hp D.odd (by omega) hK₂ α hα2 hN2 hN0 r hr w
    (fun c => c ^ p ^ D.e) hR1 hR2 hact h1 hKc M hM

theorem twE6T1NoPSp4Input_holds :
    TwE6T1NoPSp4Input := fun p _ k _ _ _ D hχ hθ J' hq =>
  (CompPred.noPSp4Odd lieOrderFormulasInput).of_model D.odd
    (twE6TwentyP_model p k D hχ hθ J' hq)

end CFSG.ComponentClassification.Burgoyne.X10
