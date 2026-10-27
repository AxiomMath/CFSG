module


public import CFSG.LocalAnalysis.RankThreeUC.Section11.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section6.SigmaSylowCentralizerEscape
import all CFSG.LocalAnalysis.RankThreeUC.Section6.SigmaSylowCentralizerEscape
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WitnessConjugacy
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ClauseBMap.ClauseBMap

public section


namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WitnessClauseB


open CFSG.Open CFSG.LocalAnalysis.RankThreeUC


theorem exists_sylow_witness_clauseB {G : Type} [Group G] [Finite G] {M T V₀ V : Subgroup G}
    (h : CFSG.LocalAnalysis.RankThreeUC.Section11.Setting G M T V₀ V) {p : ℕ}
    (hp : p ∈ CFSG.LocalAnalysis.RankThreeUC.Section6.sigmaTwoOf G M) :
    ∃ P : Sylow p G, IsWitness p P M ∧ rankThreeClauseB M (P : Subgroup G) p := by
  obtain ⟨hσ, hs2⟩ : p ∈ CFSG.LocalAnalysis.RankThreeUC.SourceSetting.sigmaOf G M ∧ SigmaTwo G p := by
    exact hp
  obtain ⟨hpA, P, hwM⟩ := hσ
  obtain ⟨-, Q, N, hwN, hB⟩ := hs2
  haveI : Fact p.Prime := ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hpA⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hN := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WitnessConjugacy.map_eq h.context.uc.standing hpA
    (P := P) (Q := Q) hwM hwN g hg
  refine ⟨P, hwM, ?_⟩
  have hPe : (P : Subgroup G) = (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact (Subgroup.pointwise_smul_def (a := MulAut.conj g) (Q : Subgroup G))
  have := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ClauseBMap.clauseB_map (MulAut.conj g) hB
  rwa [hN, ← hPe] at this


end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WitnessClauseB
