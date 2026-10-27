module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourSteps
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.LThreeParabolic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourJLeX
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.AGLEmbedding.SubnormalFStarP
import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]
variable {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ} {L : Subgroup G}

theorem twelveFourASevenLeX_of_caseTwo_or_caseSix (h : TwelveCtx G M p Q H)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H) (hd : d ∈ sigmaSet G M)
    (hcase : TwelveThreeCaseTwo M p H d ∨ TwelveThreeCaseSix M p H d)
    (hL : L ∈ weakBlockSet M H) (hB : TwelveFourBlockFacts M H L) :
    TwelveFourASevenLeX M p H L := by
  intro h5
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hp5 : 5 ≤ p := five_le_of_odd_prime_dvd_add_one h.p_prime h.p_odd
    (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1)
    (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1)
    (hcase.elim (fun h2 => h2.2.1.2.2.1) fun h6 => h6.2.2.1.2.1)
  obtain ⟨T, _, f, hf, hker⟩ := exists_charP_hom_of_caseTwo_or_caseSix h hsyl hd hcase
  have hL' : IsWeakSBlock M (pCoreOf 2 H) L := hL
  have hLM : IsSubnormal L M := hL'.subnormal
  have hle : H ⊓ L ≤ H ⊓ M := inf_le_inf le_rfl hLM.le
  have hHLM : IsSubnormal (H ⊓ L) (H ⊓ M) := by
    have h' := hLM.inf H
    rwa [inf_comm L H, inf_comm M H] at h'
  have hcop : Nat.Coprime p (Nat.card ((H ⊓ L).subgroupOf (H ⊓ M))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    refine (Nat.Prime.coprime_iff_not_dvd h.p_prime).2 fun hdvd => ?_
    rcases hB.aSeven_primes h5 p h.p_prime hdvd with h2 | h3 <;> omega
  have hC : CFSG.IsCharacteristicP p (↥(H ⊓ M) ⧸ f.ker) :=
    CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
      (QuotientGroup.quotientKerEquivRange f).symm hf
  have hV : ((H ⊓ L).subgroupOf (H ⊓ M)).IsSubnormal := (IsSubnormal.iff_subgroupOf hle).1 hHLM
  have hmap : ((H ⊓ L).subgroupOf (H ⊓ M)).map (QuotientGroup.mk' f.ker) = ⊥ :=
    eq_bot_of_isSubnormal_of_coprime_of_isCharacteristicP h.p_prime hC
      (hV.map (QuotientGroup.mk'_surjective f.ker))
      (hcop.coprime_dvd_right (card_map_dvd _ _))
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
  refine (oUpperTwo_le_self _).trans fun x hx => ?_
  exact hker ⟨x, hle hx⟩ (hmap (mem_subgroupOf.2 hx))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
