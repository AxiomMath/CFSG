module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1Main
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1Cases
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreRankTwo
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuaternionBelow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.GlueOuter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Simple

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J}

theorem Setting.nonempty_mulEquiv_alternating
    (h : Setting J Q B)
    (IH : CanonicalBelow (Nat.card J)) :
    Nonempty ((J ⧸ Subgroup.center J) ≃* alternatingGroup (Fin 9)) := by
  obtain ⟨z, hz, u, hu⟩ := h.exists_badLift
  by_cases hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)
  · obtain ⟨v, hv, T, -, -, -, L, hL, hP, -, y, hyT, hy, hyy, -, hψ, hφ⟩ :=
      hu.exists_maximalStarLift_partC_caseC3 h hz IH hrank
    exact hv.toStarLift.nonempty_mulEquiv_alternating_of_caseC3 h hz T hL hP hyT hy hyy hψ hφ
  · have h2 := hu.toEscapingLift.two_le_pRank_quasiNormalizer h hz
    exact (hu.false_of_rank_two h hz IH (by omega) (hu.quasiImage_ne_top h hz IH)).elim

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly QuasisimpleCore

theorem quasisimpleQuaternionCoreClassificationBelow :
    QuasisimpleQuaternionCoreClassificationBelow :=
  fun _ _ _ IH hperf hsimp hcard hrank _ _ hQB hB hcore hquat =>
    Or.inl ((Setting.mk hperf hsimp hcard hrank hQB hB hcore hquat).nonempty_mulEquiv_alternating
      IH)

theorem aschbacher_proper_two_generated_core_of_inputs
    (hJ9 : TwoANine.NoSimpleCentralizerTwoANine)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hrank : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G))
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* properTwoGenCoreJ1) :=
  aschbacher_proper_two_generated_core_of_quasisimpleCore
    quasisimpleQuaternionCoreClassificationBelow
    (TwoANine.noTwoANineQuaternionComponent_of_isolated
      (TwoANine.twoANineCentralizerIsolated_of_janko hJ9)) G hnonab S hrank hcore

end CFSG.ProperTwoGeneratedCore.Lemma37
