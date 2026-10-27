module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GaschutzTransfer
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.RankThree.CentralLiftU.PerfectSplit
import CFSG.RankThree.OddKernel.RankOneQuotients
import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem pRank_le_one_of_section {X S : Type*} [Group X] [Finite X] [Group S] [Finite S]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H A : Subgroup X} (hH : CFSG.Open.pRank p H ≤ 1)
    (hAH : A ≤ H) (f : ↥A →* S) (hf : Function.Surjective f) :
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 := by
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.RankThree.OddKernel.pRank_le_one_of_surjective hp hp2 f hf ?_
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact (CFSG.SectionRank.pRank_mono hp.one_lt hAH).trans hH

theorem two_le_pRank_quotient_center {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 1 := by omega
  obtain ⟨P⟩ : Nonempty (Sylow p K) := inferInstance
  have hcyc : IsCyclic ((P : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K))) :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one hp hp2 le_top (P.isPGroup'.map _)
      ((CFSG.SectionRank.pRank_coe_eq_openPRank p ⊤).trans_le h1)
  have hab := CFSG.RankThree.CentralLiftU.sylow_commute_of_isCyclic_map _
    (QuotientGroup.ker_mk' (Subgroup.center K)).le _ hcyc
  have hZ : ¬ p ∣ Nat.card (Subgroup.center K) := by
    intro hdvd
    obtain ⟨⟨z, hzZ⟩, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p hdvd
    rw [Subgroup.orderOf_mk] at hz
    refine CFSG.LocalAnalysis.RankThreeTheoremC.not_isMulCommutative_sylow_of_isPerfect
      inferInstance P hzZ ?_ (hz ▸ pow_orderOf_eq_one z)
      ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
    rintro rfl
    rw [orderOf_one] at hz
    exact hp.one_lt.ne hz
  have := CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ
  omega

end CFSG.LocalAnalysis.RankThreeUC.S15
