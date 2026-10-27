module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.SigA7
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.M22
public import CFSG.Quasithin.H13.NQCatT3Perm

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

open Subgroup CFSG.RankThree.LocalRank CFSG.Blueprint

theorem aschbacherSolvableCore_eq_bot_of_alt7 {S : Type*} [Group S] [Finite S]
    (e : S ≃* alternatingGroup (Fin 7)) : aschbacherSolvableCore 3 S = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup S := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := alt7_noncomm
  refine aschbacherSolvableCore_eq_bot_of_isSimpleGroup ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem kf148SigM22 :
    CFSG.RankThree.PartTwo.Sec14.KF148SigM22 := by
  intro Γ _ _ A L K e h hker ⟨ψ⟩
  have : IsSimpleGroup NativeSporadic.M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hna : ∃ a b : NativeSporadic.M22, a * b ≠ b * a :=
    ⟨_, _, CFSG.Sporadic.Schreier.m22_gens_not_comm⟩
  obtain ⟨K', hK', ⟨φ⟩⟩ := exists_of_inspect CFSG.Sporadic.Schreier.m22_center_eq_bot'
    (CFSG.Quasithin.H13.NQCat.T3.oddInner_of_card_le CFSG.Sporadic.Schreier.m22_center_eq_bot'
      CFSG.Sporadic.Schreier.m22_mulAut_card)
    MaximalityAmbient.KF148Sig.inspectSig148_M22
    (fun K' hK' => by
      rcases hK' with rfl | ⟨⟨e'⟩⟩
      · exact aschbacherSolvableCore_top_eq_bot hna
      · exact aschbacherSolvableCore_eq_bot_of_alt7 e')
    h hker ψ
  rcases hK' with rfl | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨φ.trans Subgroup.topEquiv⟩
  · exact Or.inr ⟨φ.trans e'⟩

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig
