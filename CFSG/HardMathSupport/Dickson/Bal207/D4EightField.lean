module

public import CFSG.HardMathSupport.Dickson.Bal207.CompShape
import all CFSG.HardMathSupport.Dickson.Bal207.CompShapeW
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFieldExport
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.HardMathSupport.Dickson.Bal207.Corr
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

@[expose] def D4EightCompIdx (d : TauCeti.LieTypeIndex) : Prop :=
  (Bal207Index 3 d ∧ ¬ IsG2EightIndex d) ∨ IsSmallTwistedIdx d ∨ IsL2EightIndex d

@[expose] def D4EightCompType (Q : Type) [Group Q] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, D4EightCompIdx d.1 ∧
    Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)

theorem isoInvariant_d4EightCompType : IsoInvariant D4EightCompType := by
  rintro Q Q' _ _ e ⟨d, hd, ⟨a⟩⟩
  exact ⟨d, hd, ⟨e.symm.trans a⟩⟩

theorem d4EightCompType_of_model_two {G : Type} [Group G]
    (hG : StatedClassicalModel G .POmegaPlus 4 2 1) : D4EightCompType G := by
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩
  have hv : (TauCeti.LieTypeIndex.D 4 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨le_rfl, fun h => h⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hG
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv (MulEquiv.refl _))
  exact ⟨⟨.D 4 q, hv⟩, Or.inl ⟨⟨rfl, Or.inr ⟨⟨rfl, rfl⟩, rfl⟩⟩, fun h => h⟩, ⟨e⟩⟩

section Field

open CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.HardMathSupport.Lang.Proving CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem d4Eight_field_comps {S : Type} [Group S] {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 8) (e₀ : S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F₀)))
    {β : MulAut S} (hβ : β ^ 3 = 1) (hout : ∀ a : S, MulAut.conj a ≠ β)
    (hE : MulAut.congr (coordinatePlusWitnessEquiv F₀ e₀) β ∈
      matrixProjectiveImage (coordinateQuadPlus 4 F₀)) :
    PerfectInLayer β ∧ ∃ J : Subgroup S,
      (∀ L : Subgroup S, IsComponentOf L (fixSubgroup β) → L = J) ∧
      Subgroup.center ↥J = ⊥ ∧ StatedClassicalModel ↥J .POmegaPlus 4 2 1 := by
  have hK : Nat.card F₀ = 2 ^ 3 := by rw [hF₀]; norm_num
  have hG : StatedClassicalModel S .POmegaPlus 4 2 3 :=
    ⟨⟨Nat.prime_two, by norm_num, le_rfl⟩, F₀, inferInstance, inferInstance, hK, ⟨e₀⟩⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 2 3 hG F₀ hK e₀
  obtain ⟨hD, hord⟩ := outer_order_prime Nat.prime_three (by norm_num)
    (coordinatePlusWitnessEquiv F₀ e₀) hgates β hβ hout
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' S .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 2 3 3 hG Nat.prime_three (by norm_num) F₀ hK e₀ _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = 3 := by rw [hUr]; exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 := by
    rw [hUr]
    exact hcard.trans (by norm_num)
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have SS := subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk Nat.prime_three
    (by norm_num) hord'' (by norm_num : 3 ≤ 4)
  have he := congr_trans_eq_fieldAutT SS _ Θ β U hUκ g' hg'l hg'r hΘ
  generalize (coordinatePlusWitnessEquiv F₀ e₀).trans Θ = φ at he
  obtain ⟨hl, hc⟩ := fieldAutT_layer_and_eq SS (by norm_num : 0 < 2 * 4)
  rw [← he] at hl hc
  set k := semilinearFixedSubfield U.val.right with hk
  have : Finite ↥k := Finite.of_injective (algebraMap k F₀) (algebraMap k F₀).injective
  obtain ⟨hsimp, a, b, hab⟩ := matrix_simple_nonabelian (by norm_num : 0 < 2 * 4) SS.hnd₀ SS.hT₀
  set J₀ := subfieldDerivedImage k SS.hext with hJ₀
  let eJ : ↥(J₀.map (φ.symm : _ →* S)) ≃* matrixProjectiveDerived (coordinateQuadPlus 4 ↥k) :=
    (J₀.equivMapOfInjective (φ.symm : _ →* S) φ.symm.injective).symm.trans
      (inclEquiv k SS.hext (by norm_num)).symm
  have : IsSimpleGroup ↥(J₀.map (φ.symm : _ →* S)) := eJ.isSimpleGroup
  refine ⟨LieSemisimple.perfectInLayer_of_congr φ β hl, J₀.map (φ.symm : _ →* S),
    fun L hL => ?_, ?_, ⟨⟨Nat.prime_two, le_rfl, le_rfl⟩, ↥k, inferInstance, inferInstance,
      hcard'.trans (by norm_num),
      ⟨eJ.trans (coordinatePlusWitnessEquiv ↥k (MulEquiv.refl _)).symm⟩⟩⟩
  · have h1 : IsComponentOf (L.map (φ : S →* _)) (fixSubgroup (MulAut.congr φ β)) := by
      rw [fixSubgroup_mulAutCongr]
      exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map φ hL
    exact ((Subgroup.map_symm_eq_iff_map_eq L).2 (hc _ h1)).symm
  · refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center _)).resolve_right
      fun htop => hab ?_
    have h1 : eJ.symm a ∈ Subgroup.center ↥(J₀.map (φ.symm : _ →* S)) :=
      htop ▸ Subgroup.mem_top _
    exact eJ.symm.injective (by rw [map_mul, map_mul]; exact (Subgroup.mem_center_iff.1 h1 _).symm)

theorem compShape_d4Eight_field {S : Type} [Group S] {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 8) (e₀ : S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F₀)))
    {β : MulAut S} (hβ : β ^ 3 = 1) (hout : ∀ a : S, MulAut.conj a ≠ β)
    (hE : MulAut.congr (coordinatePlusWitnessEquiv F₀ e₀) β ∈
      matrixProjectiveImage (coordinateQuadPlus 4 F₀)) :
    CompShape D4EightCompType β := by
  obtain ⟨hl, J, hJ, hZ, hM⟩ := d4Eight_field_comps hF₀ e₀ hβ hout hE
  refine ⟨hl, fun L hL => ?_, fun ω hω L hL => ?_⟩
  · obtain rfl := hJ L hL
    exact isoInvariant_d4EightCompType _ _
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
      (d4EightCompType_of_model_two hM)
  · exact (hJ _ (isComponentOf_map_of_commute_w hω hL)).trans (hJ L hL).symm

end Field

end CFSG.HardMathSupport.Dickson.Bal207

end
