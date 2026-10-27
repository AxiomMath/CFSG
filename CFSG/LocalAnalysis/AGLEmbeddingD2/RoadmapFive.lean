module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.RoadmapSeitz
public import CFSG.LocalAnalysis.AGLEmbeddingD2.MonsterRows
public import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridge
public import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeK
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveTrans
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveLocal
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding


theorem d2_of_five_leaves (hS : D2SeitzCross) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hLF : CFSG.CGT.PushingUpLit.AschbacherLocalFactorization)
    (hT1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (hT2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (hT25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hKB : KFactBlockAltFiveSectionInner)
    (hKS : KFactBlockAltFiveSquareInner)
    (hS3 : D2PairStrongThree)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11) (hβ : D2L34BetaCase)
    (hSzB : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      D2TransBorelAt (.lie d) fun p => p = 5)
    (hU : D2HSFiveNonBorel)
    (hFi7 : D2IndexCaseAt (.sporadic .Fi24Prime) fun p => p = 7)
    (hB7 : D2IndexCaseAt (.sporadic .B) fun p => p = 7)
    (hMon7 : D2IndexCaseAt (.sporadic .M) fun p => p = 7 ∨ p = 11 ∨ p = 13)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M := by
  have hCGT := aschbacherLocalCGTBlock_of_factorization hLF
  have hD2 := d1NoXBlock_of_inputsK hT1 hT2 hT25
  have hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      D2TorusBorelAt (.lie d) fun p => p = 5 := fun d hd =>
    d2TorusBorelAt_of_local (d2TorusLocalAt_tits d hd)
  have hSpor5 : ∀ s : TauCeti.SporadicName, s ≠ .HS → s ≠ .McL →
      D2IndexCaseAt (.sporadic s) fun p => p = 5 := by
    intro s h1 h2 G' _ _ hglob hD1' q hq
    subst hq
    refine d2SporadicCase_of_openRows' (fun s p => p = 5 ∧ s ≠ .HS) (fun s' p' hsp hQ => ?_)
      (fun G'' _ _ hglob' hD1'' q hq => d2IndexCaseAt_M_three_five G'' hglob' hD1'' q
        (Or.inr hq.1)) (d2IndexCaseAt_m11_three kFactM11Three h84 hD2 hS3)
      (d2IndexCaseAt_fi22_five kFactFi22GuestThree) s G' hglob hD1' 5
      ⟨⟨rfl, h1⟩, fun h => h2 h.1, fun h => absurd h.2 (by norm_num)⟩
    exfalso
    simp only [d2SporadicOpenList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hsp
    rcases hsp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hQ.2 rfl
    · exact absurd hQ.1 (by norm_num)
    · exact absurd hQ.1 (by norm_num)
  have hHS : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5 := d2HeisLocalEqAt_hs
  have hMcL : D2HeisLocalEqAt (.sporadic .McL) fun p => p = 5 := d2HeisLocalAt_mcl.toEq
  have hMS : D2TransMSide := d2TransMSide_of kFactThreeOrFiveDvd kFactCatalogSchreier h84 h85 h86
    h93 hD2 hK2 hC3 hK5 hKin hKP hC3p hK5p
  have hSz : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      D2IndexCaseAt (.lie d) fun p => p = 5 := fun d hd =>
    d2IndexCaseAt_sz32_five kFactLieCharRank kFactLinThreeCore hS kFactUnitarySylowStructure hMS
      h84 hCGT hD2 hSzB hTits hHS hMcL hSpor5 d hd
  have hHS5 : D2IndexCaseAt (.sporadic .HS) fun p => p = 5 :=
    d2IndexCaseAt_hs_five' kFactLieCharRank kFactLinThreeCore hS unitaryBorelKFacts
      (d2HeisMSide_of kFactThreeOrFiveDvd kFactCatalogSchreier h84 h85 h86 h93 hD2 hK2 hC3 hK5
        hKin hKP hC3p hK5p) hCGT hD2 hHS hU hTits hSzB (d2HeisBorelAt_of_local d2HeisLocalAt_mcl)
      hSpor5
  have hrows : D2SporadicOpenRows := by
    intro s q hsq
    simp only [d2SporadicOpenList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hsq
    rcases hsq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hHS5
    · exact hFi7
    · exact hB7
  exact d2_of_seitz_leaves hS h84 h85 h86 h93 (aschbacherLocalCGTBlock_of_factorization hLF)
      (d1NoXBlock_of_inputsK hT1 hT2 hT25) hK2 hC3 hK5 hKin hKP hC3p hK5p hKB hKS hS3 hJ4 hβ hSz
      hrows (d2IndexCaseAt_M_of_rows hMon7) G hnonab hK hchar he hδ₁ hδ₂ hD1 p hp P M hM' hPM Q hQ
      hQrank hQM H hH hQH

end CFSG.AGLEmbeddingD2
