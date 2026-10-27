module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BProperty
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Transport
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_piCore (G := X), ← pPrimeCore_eq_piCore (p := 2) (G := X)]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem inC_of_smallF3Cyclic (hL : SmallF3Cyclic G L) : InC L :=
  inC_of_standard hL.standard

theorem aschA1_of_smallF3Cyclic (hL : SmallF3Cyclic G L) : AschA1 G :=
  aschA1_of_balanced hL.balanced

theorem oddCore_eq_bot_of_smallF3Cyclic (hL : SmallF3Cyclic G L) : oddCore L = ⊥ := by
  have hq : IsQuasisimple L := isQuasisimple_of_standard hL.standard
  have hodd : Odd (Nat.card (oddCore L)) := odd_card_oddCore L
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (inferInstance : (oddCore L).Normal) with htop | hle
  · exfalso
    have hLodd : Odd (Nat.card L) := by
      have h := hodd
      rwa [htop, Subgroup.card_top] at h
    haveI : Group.IsPerfect L := hq.1
    haveI : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Group.IsPerfect.not_isSolvable L) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hLodd)
  · rcases hL.centre with hZ | ⟨hU, hcard⟩
    · rw [hZ] at hle
      exact le_bot_iff.mp hle
    · have hdvd : Nat.card (oddCore L) ∣ 2 := hcard ▸ Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
      · exact Subgroup.eq_bot_of_card_eq (oddCore L) h1
      · rw [h2] at hodd
        exact absurd hodd (by decide)

theorem inF_of_smallF3Cyclic (hL : SmallF3Cyclic G L)
    (hQ : SmallF3OmegaQuotient (L ⧸ center L)) : InF L := by
  have hq : IsQuasisimple L := isQuasisimple_of_standard hL.standard
  have hO : oddCore L = ⊥ := oddCore_eq_bot_of_smallF3Cyclic hL
  refine ⟨hq, ?_⟩
  rcases hL.centre with hZ | ⟨hU, hcard⟩
  · left
    exact smallF3OmegaQuotient_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (hZ.trans hO.symm)) hQ
  · right
    have h2u : IsTwoU43 L := ⟨hcard, hU⟩
    let e : (L ⧸ oddCore L) ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
    exact isTwoU43_of_mulEquiv e.symm h2u

end CFSG.OddStandard.SmallF3.Omega
