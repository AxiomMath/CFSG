module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8Gen
public import CFSG.Sporadic.ONOddCore.LocalComp
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC.ResidualA8

open CFSG CFSG.LocalCores CFSG.ONSchreier CFSG.Sporadic.ONOddCore

section ON


theorem s3_statedClassicalModel :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel S3 .PSL 3 2 2 := by
  refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, PSL3Four.F4,
    inferInstance, inferInstance, card_F4, ⟨?_⟩⟩
  exact (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
    3 PSL3Four.F4).symm.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 PSL3Four.F4)

theorem s3_not_equiv_alt_eight : ¬ Nonempty (S3 ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨φ⟩
  exact ((CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated S3
    s3_statedClassicalModel).2.2 (Fin 8) (by simp)).false φ

theorem noAltEightComponent_onM : NoAltEightComponent onM := by
  have hker : Group.IsSolvable piR.ker := by
    rw [ker_piR]
    have hp : IsPGroup 2 (onQ.subgroupOf onM) :=
      IsPGroup.of_card (n := 2) (by rw [card_onQ_subgroupOf_M]; norm_num)
    have : Group.IsNilpotent (onQ.subgroupOf onM) := hp.isNilpotent
    infer_instance
  refine NoAltEightComponent.of_surjective_simple piR piR_surjective hker XR XR_index XR_simple
    XR_noncomm ?_
  rintro ⟨φ⟩
  exact s3_not_equiv_alt_eight ⟨(XREquiv.trans thetaX.symm).symm.trans φ⟩

theorem noAltEightComponent_on_centralizer {T : Type*} [Group T]
    (hT : Nonempty (T ≃* Blueprint.NativeSporadic.ON)) (t : T) (ht : orderOf t = 2) :
    NoAltEightComponent (Subgroup.centralizer ({t} : Set T)) := by
  obtain ⟨e⟩ := hT
  set f : T ≃* Pv := e.trans onEquivPv
  have hft : orderOf (f t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ht
  obtain ⟨g⟩ := centralizer_P_equiv_M hft
  exact NoAltEightComponent.of_mulEquiv ((centralizerCongr f t).trans g) noAltEightComponent_onM

end ON

end CFSG.ComponentClassification.CatFC.ResidualA8
