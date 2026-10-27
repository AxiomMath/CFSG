module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourSteps
public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]
variable {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ} {L : Subgroup G}

omit [Finite G] in
theorem TwelveThreeCaseSpor.ne_three (hc : TwelveThreeCaseSpor M p H d) : d ≠ 3 := by
  rcases hc.2.2.1 with h3 | h4 | h5
  · rcases h3 with ⟨-, -, hd, -⟩
    omega
  · rcases h4.2 with ⟨-, hd, -⟩ | ⟨-, hd, -⟩ <;> omega
  · rcases h5.2 with ⟨-, hd, -⟩ | ⟨-, hd, -⟩ <;> omega

theorem twelveFourStepA_of_blocks (h : TwelveCtx G M p Q H) (hd : d ∈ sigmaSet G M)
    (hB : TwelveFourBlockFacts M H L)
    (h3 : 3 ∈ sigmaSet G M → ¬ 3 ∣ Nat.card (xSub p M H) ∧ jOne H L ≤ xSub p M H ∧
      TwelveFourASevenLeX M p H L) : TwelveFourStepA M d := by
  have h3σ : 3 ∉ sigmaSet G M := by
    intro h3m
    obtain ⟨hX3, hJX, hA7⟩ := h3 h3m
    have hdvd : 3 ∣ Nat.card (xSub p M H) := by
      by_cases h935 : NineThreeFive M L
      · have h3dvd : 3 ∣ Nat.card (H ⊓ L : Subgroup G) := by
          simpa only [inf_comm] using hB.three_dvd
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ L)) 3 h3dvd
        have hxO : (x : G) ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (H ⊓ L) :=
          Subgroup.subset_closure ⟨x.2, by rw [Subgroup.orderOf_coe, hx]; norm_num⟩
        have hord : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
        rw [← hord]
        exact Subgroup.orderOf_dvd_natCard (xSub p M H) (hA7 h935 hxO)
      · obtain ⟨I, hI⟩ := hB.cZero_nonempty h935
        exact (hB.three_dvd_oUpperTwo I hI).trans
          ((Subgroup.card_dvd_of_le (IsCZeroMember.oUpperTwo_le_jOne hI)).trans
            (Subgroup.card_dvd_of_le hJX))
    exact hX3 hdvd
  refine ⟨h3σ, h.cstar.pRank_le_three_of_not_mem_sigmaSet h.maxLocal Nat.prime_three
    (by norm_num) h3σ, ?_⟩
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hd2 : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  have hd3 : d ≠ 3 := fun hd3 => h3σ (hd3 ▸ hd)
  exact hdp.five_le_of_ne_two_of_ne_three hd2 hd3

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
