module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Main
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.D44Outer
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridge
public import CFSG.HardMathSupport.Dickson.Bal207.Corr
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.L2Eight
public import CFSG.LieType.SeitzGeneration.Dispatch
public import CFSG.LieType.SeitzGeneration.Hyper
public import CFSG.LieType.SeitzGeneration.HyperBridge
public import CFSG.RankThree.PartTwo.KFacts.K72OutL2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2

theorem i271ChevQ_of_inputs_simple
    (hS2 : KFactSeitzRankTwo)
    (hS3 : Seitz2310CubeSimple) (hGA : CFSG.Open.GriessAllModelsStatement)
    (h2318 : Gen2318) (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr) (h209Two : Bal209Two) (h209F4 : Bal209F4Eight)
    (hOut4 : ChevQOuterFour) (hE64 : ChevQTwistedE6Four) : I271ChevQ := by
  classical
  intro X _ _ hXK p K B hH hNorm hNA hLie hL34
  obtain ⟨d, ⟨e⟩, hdp⟩ := hLie
  have hBN : B ≤ Subgroup.normalizer (K : Set X) := hNorm.1
  have hBel : IsElemAbelian p B := hH.scp.2.1
  have hKc : CFSG.Open.IsComponentOf K ⊤ := i116pI_isComponentOf hH.core hH.comp
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hOK : GLAPPrimeCore p ↥K = ⊥ := i271h_primeCore_eq_bot hH.core hH.comp
  have hZ : CFSG.Open.pRank p (Subgroup.center ↥K) ≤ 1 :=
    center64_of_griess hGA p hH.prime hH.odd ↥K hq hOK d ⟨e⟩ hdp.symm
  by_cases hc3 : 3 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X))
  · exact Or.inl ⟨hH.rank_four, isInGOne_of_centralizing hBN inf_le_left inf_le_right hc3⟩
  have hc1 : 1 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)) :=
    one_le_pRank_centralizer hH.prime hBel hH.centralized
  by_cases hc2 : 2 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X))
  ·
    by_cases hexc : IsD2SeitzException p d.1
    · rcases l28_or_bal207_or_l34_of_d2Exc hexc with ⟨hp3, hL28⟩ | h207i | ⟨hp3, q, hdq, hq2⟩
      · subst hp3
        exact Or.inr (isStronglyBalanced_of_l2Eight hH hNorm ⟨d, hL28, ⟨e⟩⟩)
      · exact Or.inr (h207 X hXK p K B hH.prime hH.odd hKc hH.scp hBN d h207i ⟨e⟩
          fun hg => (CFSG.HardMathSupport.Dickson.Bal207.not_isG2EightIndex_of_d2Exc hexc hg).elim)
      · exact (hL34 ⟨hp3, isLThreeFour_of_index d q hdq hq2 e⟩).elim
    · exact Or.inl (caseA_of_plane hS2 hH hNorm hc2 hZ d e hdp.symm hexc)
  have hc : CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)) = 1 := by omega
  have hcube : ∀ E : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)), E ≤ autImage B K →
      IsElemAbelian p E → Nat.card E = p ^ 3 →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →*
        MulAut (↥K ⧸ Subgroup.center ↥K)).range)) → seitzHyperGamma p E = ⊤ :=
    fun E _ hEel hEcard hex => seitz2310_of_quasisimple hS3 hH.prime hH.odd hq d e hdp.symm hL34 E hEel hEcard hex
  by_cases hex : ExcIndex p d.1
  · rcases hex with h207i | ⟨hp3, hL28 | h2318i | hE62 | hE64i | hSix⟩
    · have h4 := hH.rank_four
      exact Or.inr (h207 X hXK p K B hH.prime hH.odd hKc hH.scp hBN d h207i ⟨e⟩ fun _ => by omega)
    · subst hp3
      exact Or.inr (isStronglyBalanced_of_l2Eight hH hNorm ⟨d, hL28, ⟨e⟩⟩)
    · subst hp3
      obtain ⟨-, hG⟩ := h2318 X hXK K B hKc hBel hBN hH.rank_local hH.centralized
        ⟨d, h2318i, ⟨e⟩⟩
      exact Or.inl ⟨hH.rank_four, isInGOne_of_gammaPrime_four hBN hG⟩
    · subst hp3
      exact Or.inr (h209Two X hXK K B hKc hH.scp hBN hH.rank_local ⟨d, hE62, ⟨e⟩⟩)
    · subst hp3
      exact hE64 X hXK K B hH hNorm ⟨d, hE64i, ⟨e⟩⟩
    · subst hp3
      by_cases hinn : InducesInnerIn B K
      · exact Or.inl (caseA_of_cube hH hBN hc hZ fun E hEA hEel hEcard =>
          hcube E hEA hEel hEcard (Or.inr ⟨hSix, hEA.trans (autImage_le_range_conj hinn)⟩))
      · rcases hSix with hF4 | hD4 | hFour
        · exact Or.inr (h209F4 X hXK K B hKc hH.scp hBN hH.rank_local ⟨d, hF4, ⟨e⟩⟩ hinn)
        · exact (false_of_d44_outer d44OuterRank_holds hH hBN ⟨d, hD4, ⟨e⟩⟩ hinn).elim
        · exact hOut4 X hXK K B hH hNorm ⟨d, hFour, ⟨e⟩⟩ hinn
  · exact Or.inl (caseA_of_cube hH hBN hc hZ fun E hEA hEel hEcard =>
      hcube E hEA hEel hEcard (Or.inl hex))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
