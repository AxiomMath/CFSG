module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2Inspect
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Reduction
public import CFSG.Quasithin.H13.NQCatT3Perm
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

open Subgroup CFSG.ComponentClassification.J2Cover CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

theorem oddInner_GJ :
    ∀ α : MulAut GJ, Odd (orderOf α) → ∃ g : GJ, α = MulAut.conj g := by
  apply CFSG.Quasithin.H13.NQCat.T3.oddInner_of_card_le center_P
  rw [card_mulAut_P, card_GJ]

theorem kf148SigHJ :
    CFSG.RankThree.PartTwo.Sec14.KF148SigHJ := by
  intro Γ _ _ A L K e h hker ⟨ψ⟩
  have : IsSimpleGroup GJ := isSimpleGroup_P
  obtain ⟨K', hK', ⟨φ⟩⟩ := exists_of_inspect center_P oddInner_GJ J2.inspectSig148_GJ
    (fun K' hK' => hK' ▸ aschbacherSolvableCore_top_eq_bot ⟨pa, pb, pa_pb_ne⟩) h hker
    (ψ.trans nativeEquivP)
  subst hK'
  exact ⟨φ.trans (Subgroup.topEquiv.trans nativeEquivP.symm)⟩

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig
