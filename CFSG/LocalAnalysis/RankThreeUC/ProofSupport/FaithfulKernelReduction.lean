module


public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.IrreducibleRankCentralization
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.NormalizerKernelDichotomy.NormalizerKernelDichotomy
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddQuotientCentralizes.OddQuotientCentralizes
public import CFSG.LocalAnalysis.RankThreeUC.Section12.NoncyclicCentralizerTI
public import CFSG.LocalAnalysis.RankThreeUC.Section11.ContextEquivalence
public import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport

public section


namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.FaithfulKernelReduction


open Subgroup CFSG.LocalAnalysis.RankThreeUC


variable {G : Type} [Group G] [Finite G]


theorem inf_kernel_eq_bot {M T V₀ V : Subgroup G} (h : Section11.Setting G M T V₀ V)
    {p : ℕ} (hp : p ∈ SourceSetting.sigmaOf G M) {X : Subgroup G} (hXp : IsPGroup p X)
    (hXM : X ≤ M) (hrank : 1 < CFSG.Open.pRank p X)
    (hirr : Section6.IsIrreducibleUnder (M ⊓ normalizer (X : Set G)) X) :
    X ⊓ centralizerOnQuotient M V₀ V = ⊥ := by
  obtain ⟨hpp, hp2, -⟩ := Section12.NonTISigmaPrimeRank.sigma_prime_rank hp
  have hfacts : V ∈ normalElemAbelian2 M ∧ V₀ ≤ V := by
    rcases h.moduleChoice with hm | ⟨h1, h2⟩
    · exact ⟨hm.2.1, hm.2.2.1⟩
    · exact ⟨normalElemAbelian2One_subset M T (weakModules_subset M T h1), h2 ▸ bot_le⟩
  obtain ⟨hV, hle⟩ := hfacts
  have hVn : M ≤ normalizer (V : Set G) := (mem_normalElemAbelian2.mp hV).2.2.2
  have hV₀ : M ≤ normalizer (V₀ : Set G) := by
    rcases h.moduleChoice with hm | ⟨-, h0⟩
    · exact (mem_normalElemAbelian2.mp hm.1).2.2.2
    · subst h0
      intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp
  have hexp : ∀ v ∈ V, v ^ 2 = 1 := (mem_normalElemAbelian2.mp hV).2.1.2
  have hKM : M ⊓ normalizer (X : Set G) ≤ M := inf_le_left
  have hKX : M ⊓ normalizer (X : Set G) ≤ normalizer (X : Set G) := inf_le_right
  rcases NormalizerKernelDichotomy.kernel_eq_bot_or_le hXM hKM hKX hVn hV₀ hirr with hb | hq
  · exact hb
  · exfalso
    have h0 := IrreducibleRankCentralization.centralizes_base h hp hXp hXM hrank hirr hKM hKX
    have hc := OddQuotientCentralizes.centralizes hpp hp2 hXp hle hexp h0 hq
    have hle' : X ≤ M ⊓ centralizer (V : Set G) := le_inf hXM hc
    apply h.not_TI
    exact Section12.NoncyclicCentralizerTI.isTI_of_one_lt_pRank_centralizer
      h.context.toSection12 hV hp
      (lt_of_lt_of_le hrank (PrimeRankSylowTransport.pRank_le_of_le hpp hle'))


end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.FaithfulKernelReduction
