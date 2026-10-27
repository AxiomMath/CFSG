module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClFix
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGClosureLayer
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutSurj
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModel
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK0
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK3
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK0
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK3
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClGroup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem fg_facts_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    Finite ↥(omegaProj hQ) ∧ CFSG.IsQuasisimple ↥(omegaProj hQ) ∧
      IsFStarGroup ↥(omegaProj hQ) := by
  have hLie := ff_lieModel_omegaProj_six_plus hQ hdim hs
  have hfs := CFSG.LieType.Simplicity.fam_classical_converse (omegaProj hQ)
    ⟨.PSL, 4, 3, 1, hLie.statedClassicalModel_of_ne_zero (by norm_num)⟩
  haveI := hfs.1
  have hsimple : IsSimpleGroup ↥(omegaProj hQ) := hfs.2.2
  have hcard := ff_natCard_omegaProj_six_plus hQ hdim hs
  have hnc := ff_noncomm_of_simple_card hsimple (by rw [hcard]; norm_num)
  have hq := ff_isQuasisimple_of_simple hsimple hnc
  have hquot := ff_lieModel_quot_oddCore hLie hsimple (by rw [hcard]; norm_num)
  exact ⟨hfs.1, hq, Or.inl ⟨hq, Or.inl (Or.inr (Or.inl hquot))⟩⟩

private theorem fg_facts_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    Finite ↥(omegaProj hQ) ∧ CFSG.IsQuasisimple ↥(omegaProj hQ) ∧
      IsFStarGroup ↥(omegaProj hQ) := by
  have hLie := ff_lieModel_omegaProj_six_minus hQ hdim hs
  have hfs := CFSG.LieType.Simplicity.fam_classical_converse (omegaProj hQ)
    ⟨.PSU, 4, 3, 1, hLie.statedClassicalModel_of_ne_zero (by norm_num)⟩
  haveI := hfs.1
  have hsimple : IsSimpleGroup ↥(omegaProj hQ) := hfs.2.2
  have hcard := ff_natCard_omegaProj_six_minus hQ hdim hs
  have hnc := ff_noncomm_of_simple_card hsimple (by rw [hcard]; norm_num)
  have hq := ff_isQuasisimple_of_simple hsimple hnc
  have hquot := ff_lieModel_quot_oddCore hLie hsimple (by rw [hcard]; norm_num)
  exact ⟨hfs.1, hq, Or.inl ⟨hq, Or.inl (Or.inr (Or.inr (Or.inl hquot)))⟩⟩

theorem fg_closureFix_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    ClosureFix ↥(omegaProj hQ) := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨hfin, hq, hF⟩ := fg_facts_six_plus hQ hdim hs
  haveI := hfin
  have hbij := ffSimOmegaAct_bijective_six_plus hQ hdim hs
  refine closureFix_of_ne_one hq hF ?_
  intro α hα hα1 J hJ
  obtain ⟨x, rfl⟩ := hbij.2 α
  have hx2 : x * x = 1 := hbij.1 (by rw [map_mul, map_one]; exact hα)
  have hJ' : IsComponentIn J (ffFix hQ h2 x) := hJ
  rcases ff_model_classify hQ hdim hs hx2 with h | h | h | h | h | h
  · exact absurd (by rw [h, map_one]) hα1
  · exact absurd (ff_K0_solvable hQ hdim hs h) hJ'.not_isSolvable
  · exact fg_inFStar_of_layerModel fg_shape_psl2 (ff_K1_layerModel hQ hdim hs h) hJ'
  · exact fg_inFStar_of_layerModel fg_shape_psp (ff_K2_layerModel hQ hdim hs h) hJ'
  · exact absurd (ff_K3_solvable hQ hdim hs h) hJ'.not_isSolvable
  · rcases ff_K4_layerModel hQ hdim hs hx2 h with h' | h'
    · exact fg_inFStar_of_layerModel fg_shape_psl3 h' hJ'
    · exact fg_inFStar_of_layerModel fg_shape_psl2 h' hJ'

theorem fg_closureFix_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    ClosureFix ↥(omegaProj hQ) := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨hfin, hq, hF⟩ := fg_facts_six_minus hQ hdim hs
  haveI := hfin
  have hbij := ffSimOmegaAct_bijective_six_minus hQ hdim hs
  refine closureFix_of_ne_one hq hF ?_
  intro α hα hα1 J hJ
  obtain ⟨x, rfl⟩ := hbij.2 α
  have hx2 : x * x = 1 := hbij.1 (by rw [map_mul, map_one]; exact hα)
  have hJ' : IsComponentIn J (ffFix hQ h2 x) := hJ
  rcases ff6m_model_classify hQ hdim hs hx2 with h | h | h | h | h | h | h
  · exact absurd (by rw [h, map_one]) hα1
  · exact absurd (ff6m_K0_solvable hQ hdim hs h) hJ'.not_isSolvable
  · exact fg_inFStar_of_layerModel fg_shape_psl2 (ff6m_N1_layerModel hQ hdim hs h) hJ'
  · exact fg_inFStar_of_layerModel fg_shape_psp (ff6m_K2_layerModel hQ hdim hs h) hJ'
  · exact absurd (ff6m_K3_solvable hQ hdim hs h) hJ'.not_isSolvable
  · exact fg_inFStar_of_layerModel fg_shape_psu3 (ff6m_N2_layerModel hQ hdim hs h) hJ'
  · exact fg_inFStar_of_layerModel fg_shape_psl2 (ff6m_K4_layerModel hQ hdim hs hx2 h) hJ'

end CFSG.OddStandard.SmallF3.Omega
