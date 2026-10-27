module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.Cores
public import CFSG.RankThree.PartTwo.KFacts.KP4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig

open Subgroup CFSG CFSG.GH74.GLS CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.Blueprint CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

theorem inspectSig148_M22 :
    InspectSig148 NativeSporadic.M22
      (fun K => K = ⊤ ∨ Nonempty (↥K ≃* alternatingGroup (Fin 7))) := by
  intro E K hE hexp hEK hperf hK1 hKle
  have hcommE := comm_of_card_nine E hE
  obtain ⟨F, hF, -, hFK⟩ := sSup_cores_eq E K hcommE hEK hKle
  have hL : Nonempty (↥NativeSporadic.M22 ≃* NativeSporadic.M22) := ⟨MulEquiv.refl _⟩
  rcases KFacts.KP4.m22_sSup_cases hL hE F hF with h | ⟨-, h⟩ | h
  · rw [hFK] at h
    exfalso
    have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK1
    have : Group.IsSolvable K := by
      have := h.isNilpotent
      infer_instance
    exact Group.IsPerfect.not_isSolvable K inferInstance
  · rw [hFK] at h
    exact Or.inr h
  · rw [hFK] at h
    exact Or.inl h

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig
