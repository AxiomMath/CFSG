module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Reduction
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.A7
public import CFSG.Quasithin.H13.NQCatT3A7

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

open Equiv Subgroup CFSG.RankThree.LocalRank

theorem alt7_noncomm : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
  refine ⟨⟨swap 0 2 * swap 0 1, Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨swap 2 4 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩, fun h => ?_⟩
  have h' := congrArg Subtype.val h
  revert h'
  decide

theorem kf148SigA7 :
    CFSG.RankThree.PartTwo.Sec14.KF148SigA7 := by
  intro Γ _ _ A L K e h hker ⟨ψ⟩
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨K', hK', ⟨φ⟩⟩ := exists_of_inspect (center_eq_bot_of_isSimpleGroup alt7_noncomm)
    CFSG.Quasithin.H13.NQCat.T3.oddInner_alt7 A7.inspectSig148_alt7
    (fun K' hK' => hK' ▸ aschbacherSolvableCore_top_eq_bot alt7_noncomm) h hker ψ
  subst hK'
  exact ⟨φ.trans Subgroup.topEquiv⟩

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig
