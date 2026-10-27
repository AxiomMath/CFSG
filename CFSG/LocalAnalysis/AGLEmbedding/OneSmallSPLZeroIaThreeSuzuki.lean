module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePPrime

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem kFactSuzukiThreeCent_of_pPrimeCompInvolution (hK : KFactPPrimeCompInvolutionP) :
    KFactSuzukiThreeCent := by
  intro Y _ _ L hL hcat hcop u huN hu3 huC
  obtain ⟨j, hjL, hj1, hj2, hju, -⟩ := hK Y 3 Nat.prime_three (by norm_num) L
    ((CFSG.isComponent_iff_open L).mpr hL) hcat
    (fun h => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
      (h.trans (Subgroup.index_dvd_card _)))
    ⊥ u bot_le
    (fun a ha => by
      rw [Subgroup.mem_bot] at ha
      rw [ha, one_pow]
      exact one_mem _)
    huN hu3
    (fun t ht => by
      rw [Subgroup.mem_bot] at ht
      rw [ht, one_mul, mul_one])
    huC
  have hjC : j ∈ L ⊓ Subgroup.centralizer ({u} : Set Y) :=
    ⟨hjL, Subgroup.mem_centralizer_singleton_iff.mpr hju⟩
  have hord : orderOf (⟨j, hjC⟩ : ↥(L ⊓ Subgroup.centralizer ({u} : Set Y))) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hj2))
      (fun h => hj1 (by simpa using congrArg Subtype.val h))
  exact hord ▸ orderOf_dvd_natCard _

end CFSG.AGLEmbedding
