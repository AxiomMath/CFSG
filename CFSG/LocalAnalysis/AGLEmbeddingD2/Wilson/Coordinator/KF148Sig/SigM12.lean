module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Reduction
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.M12
public import CFSG.Quasithin.H13.NQCatT3Perm

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

open Subgroup CFSG.RankThree.LocalRank CFSG.Blueprint

theorem kf148SigM12 :
    CFSG.RankThree.PartTwo.Sec14.KF148SigM12 := by
  intro Γ _ _ A L K e h hker ⟨ψ⟩
  have : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have hna : ∃ a b : NativeSporadic.M12, a * b ≠ b * a :=
    ⟨_, _, CFSG.Sporadic.Schreier.m12_gens_not_comm⟩
  obtain ⟨K', hK', ⟨φ⟩⟩ := exists_of_inspect CFSG.Sporadic.Schreier.m12_center_eq_bot'
    (CFSG.Quasithin.H13.NQCat.T3.oddInner_of_card_le CFSG.Sporadic.Schreier.m12_center_eq_bot'
      CFSG.Sporadic.Schreier.m12_mulAut_card)
    MaximalityAmbient.KF148Sig.inspectSig148_M12
    (fun K' hK' => hK' ▸ aschbacherSolvableCore_top_eq_bot hna) h hker ψ
  subst hK'
  exact ⟨φ.trans Subgroup.topEquiv⟩

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig
