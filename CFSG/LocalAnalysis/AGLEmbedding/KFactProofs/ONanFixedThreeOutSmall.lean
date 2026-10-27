module

public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.KC.UnitaryPlaneStatements
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeProof
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary

public section

namespace CFSG.AGLEmbedding.FixedThree

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open TauCeti

theorem primePower_eq_of_card_three {q : PrimePower} (h : q.card = 3) :
    q.p = 3 ∧ q.exponent = 1 := by
  have h1 : q.p ^ q.exponent = 3 := (PrimePower.card_def q).symm.trans h
  have hp : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1
    (h1 ▸ dvd_pow_self _ q.exponent_pos.ne')
  rw [hp] at h1
  exact ⟨hp, Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h1)⟩

theorem not_three_dvd_card_outer_twistedA_three {K : Type} [Group K] (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 3)
    (e : K ≃* (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) : ¬ 3 ∣ Nat.card (Outer K) := by
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
  obtain ⟨-, -, hn3, hne, F, _, hU, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU hm
  have := hU.finite
  rw [Nat.card_congr (equivalence θ).toEquiv]
  intro h3
  have hd := h3.trans (CFSG.RankThree.PartTwo.Sec4.card_outer_primeFormP_dvd hU hn3 hne)
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_three hq
  rw [hp, hf] at hd
  norm_num at hd

section TauCetiExceptional

theorem not_three_dvd_card_outer_G2_three {K : Type} [Group K] (q : PrimePower)
    (hv : (LieTypeIndex.G2 q).Valid) (hq : q.card = 3)
    (e : K ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : ¬ 3 ∣ Nat.card (Outer K) := by
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_three hq
  have hmodel : CFSG.Blueprint.ChevalleyExceptionalModel K .G2 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩,
      CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.g2 q hv
        (by omega) e⟩
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
  rw [hp, hf] at hmodel
  rw [CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree.card_outer_G2_three K hmodel]
  norm_num

end TauCetiExceptional

end CFSG.AGLEmbedding.FixedThree
