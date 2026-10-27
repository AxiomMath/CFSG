module

public import CFSG.ClassicalInvolution.LBalance.Glauberman
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.PGroups
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Relations

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
  CFSG.ComponentClassification.AschbacherToolkit
open scoped commutatorElement

theorem glaubermanSylowFixedSolvable_proved : GlaubermanSylowFixedSolvable := by
  intro X _ _ hX heven S A hA
  have hcore : CFSG.pPrimeCore 2 X = ⊥ := by
    rw [CFSG.ClassicalInvolution.pPrimeCore_two_eq_oddCore X, CFSG.oddCore, sSup_eq_bot]
    rintro N ⟨hN, hodd⟩
    rcases hN.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) heven
  have hAle : A ≤ CFSG.ClassicalInvolution.sylowFixingAut (S : Subgroup X) :=
    fun α hα => CFSG.ClassicalInvolution.mem_sylowFixingAut.2 (hA α hα)
  haveI : Group.IsSolvable (CFSG.ClassicalInvolution.sylowFixingAut (S : Subgroup X)) :=
    CFSG.ClassicalInvolution.glaubermanSylowFixingSolvable X hcore S
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAle)

theorem glaubermanSimplePerfect_proved : GlaubermanSimplePerfect :=
  glaubermanSimplePerfect_of_sylowFixedSolvable glaubermanSylowFixedSolvable_proved

theorem two_le_pRank_of_ne_one {H : Type} [Group H] [Finite H] {K : Subgroup H} (hK : InLF K)
    (h : CFSG.pRank 2 ↥K ≠ 1) : 2 ≤ CFSG.Open.pRank 2 K := by
  have hq := hK.isQuasisimple
  have heven : Even (Nat.card (↥K ⧸ Subgroup.center ↥K)) := by
    haveI : Group.IsPerfect ↥K := hq.1
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2.1
    by_contra hodd
    exact Group.IsPerfect.not_isSolvable (↥K ⧸ Subgroup.center ↥K)
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd))
  have h2dvd : 2 ∣ Nat.card ↥K := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)]
    exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp heven) _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv2⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h2dvd
  have hv2' : v ^ 2 = 1 := by simpa [hv2] using pow_orderOf_eq_one v
  have hE : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers v) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv2', one_zpow]
  have h1 : 1 ≤ CFSG.Open.pRank 2 K := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
    refine CFSG.SectionRank.le_pRank (by norm_num) le_top hE ?_
    rw [Nat.card_zpowers, hv2]
    norm_num
  have hbridge : CFSG.pRank 2 ↥K = CFSG.Open.pRank 2 K :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥K).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
  have hne : CFSG.Open.pRank 2 K ≠ 1 := fun h1' => h (hbridge.trans h1')
  omega

end CFSG.EvenSporadicStandard.Induction.ThmU
