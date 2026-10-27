module


public import CFSG.LocalAnalysis.RankThreeUC.Section6.SigmaSylowCentralizerEscape
import all CFSG.LocalAnalysis.RankThreeUC.Section6.SigmaSylowCentralizerEscape
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ClauseBLayerAction.ClauseBLayerAction
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.FaithfulKernelReduction
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WitnessClauseB

public section


namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ClauseBFaithfulData


open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC


theorem exists_data {G : Type} [Group G] [Finite G] {M T V₀ V : Subgroup G}
    (h : CFSG.LocalAnalysis.RankThreeUC.Section11.Setting G M T V₀ V) {p : ℕ}
    (hp : p ∈ CFSG.LocalAnalysis.RankThreeUC.Section6.sigmaTwoOf G M) :
    ∃ (P : Sylow p G) (P₀ : Subgroup G),
      IsWitness p P M ∧ rankThreeClauseB M (P : Subgroup G) p ∧
      P₀ ≤ (P : Subgroup G) ∧ Nat.card P₀ = p ∧
      CFSG.Quasithin.IsWeaklyClosedIn P₀ (P : Subgroup G) ∧
      CFSG.LocalAnalysis.RankThreeUC.Section6.SigmaSylowCentralizerEscape G M T p (P : Subgroup G) P₀ ∧
      p.Prime ∧ 5 ≤ p ∧ Group.IsSolvable M ∧
      (∃ (_ : Fact p.Prime) (n : ℕ), 1 < n ∧
        Nonempty (↥(rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p n))) ∧
      ¬ rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≤ M ∧
      rankThreeFrobeniusProduct (rankThreePrimeCore p M) (pCoreOf 2 M)
        (Subgroup.centralizer (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ∧
      ((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≤ M ∧
      IsPGroup p ↥((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) ∧
      1 < CFSG.Open.pRank p ((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) ∧
      Subgroup.normalizer (((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Subgroup G) : Set G) ≤ M ∧
      CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder
        (M ⊓ Subgroup.normalizer (((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Subgroup G) : Set G))
        ((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) ∧
      ((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) ⊓ centralizerOnQuotient M V₀ V = ⊥) := by
  obtain ⟨P, hw, hB⟩ := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WitnessClauseB.exists_sylow_witness_clauseB h hp
  have hp' : p ∈ CFSG.LocalAnalysis.RankThreeUC.SourceSetting.sigmaOf G M ∧ SigmaTwo G p := hp
  have hpA : p ∈ rankThreeSigmaA G := hp'.1.1
  have hprime : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hpA
  haveI : Fact p.Prime := ⟨hprime⟩
  have hPM : (P : Subgroup G) ≤ M := hw.sylow_le h.context.uc.standing hpA
  have hSylM : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) M := by
    have h1 : IsPGroup p ((P : Subgroup G).subgroupOf M) := P.isPGroup'.comap_subtype
    have h2 : ¬ p ∣ ((P : Subgroup G).subgroupOf M).index := by
      intro hd
      have h3 := (Subgroup.relIndex_dvd_index_of_le hPM)
      exact P.not_dvd_index (dvd_trans (show p ∣ (P : Subgroup G).relIndex M from hd) h3)
    refine ⟨h1.toSylow h2, ?_⟩
    simpa using Subgroup.map_subgroupOf_eq_of_le hPM
  have hB2 := hB
  obtain ⟨hp5, hsolv, P₀, hle, hcard, hweak, ⟨hF, n, hn, ⟨e⟩⟩, hnl, hfrob, -⟩ := hB2
  have hlayer : rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≤
      Subgroup.centralizer (P₀ : Set G) := by
    refine sSup_le ?_
    rintro L ⟨hL, -, -⟩
    exact hL
  have hH : CFSG.LocalAnalysis.RankThreeUC.Section6.SigmaSylowCentralizerEscape G M T p (P : Subgroup G) P₀ :=
    ⟨⟨h.context.uc, h.context.mSigma, h.context.sylow⟩, hprime, hp, hSylM, hle, hcard,
      fun hc => hnl (hlayer.trans hc)⟩
  obtain ⟨-, -, -, hrank, hN, hirr⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ClauseBLayerAction.layer_action hpA P hw hle hcard hweak hp5
      (by omega) ⟨e⟩
  have hXp : IsPGroup p ↥((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) :=
    P.isPGroup'.to_le inf_le_left
  have hXM : (P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≤ M :=
    inf_le_left.trans hPM
  refine ⟨P, P₀, hw, hB, hle, hcard, hweak, hH, hprime, hp5, hsolv, ⟨hF, n, hn, ⟨e⟩⟩, hnl, hfrob,
    hXM, hXp, hrank, hN, hirr, ?_⟩
  exact CFSG.LocalAnalysis.RankThreeUC.ProofSupport.FaithfulKernelReduction.inf_kernel_eq_bot h hH.sigma2.1 hXp hXM
    hrank hirr


end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ClauseBFaithfulData
