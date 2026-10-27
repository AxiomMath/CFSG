module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PRankSurvivor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.OddCoversTable
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.OddCoversRank
public import CFSG.Alternating.Multipliers.Small
public import CFSG.Quasithin.Background.F918G1

public section

namespace CFSG.Quasithin.B69K.OddCovers

open CFSG.Open CFSG.RankThree.PerfectCover CFSG.Quasithin

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨hc, hs⟩ := h
  have hperf : Group.IsPerfect Q := ⟨hc⟩
  refine ⟨hperf, hs, ?_⟩
  by_contra hne
  push Not at hne
  have hcomm : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a := hne
  have hbot : commutator (Q ⧸ Subgroup.center Q) = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _ b _
    exact (hcomm b a)
  have htop : commutator (Q ⧸ Subgroup.center Q) = ⊤ := by
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center Q))) hc
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
    rw [_root_.commutator_def]
    exact h2
  have : Nontrivial (Q ⧸ Subgroup.center Q) := hs.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  have hx' : x ∈ commutator (Q ⧸ Subgroup.center Q) := by
    rw [htop]
    exact Subgroup.mem_top x
  rw [hbot, Subgroup.mem_bot] at hx'
  exact hx hx'

theorem eq_one_of_odd_of_dvd_four {n : ℕ} (hn : Odd n) (h : n ∣ 4) : n = 1 := by
  have hle : n ≤ 4 := Nat.le_of_dvd (by norm_num) h
  rw [Nat.odd_iff] at hn
  interval_cases n <;> omega

theorem eq_three_of_odd_of_dvd_six {n : ℕ} (hn : Odd n) (h : n ∣ 6) (h1 : 1 < n) : n = 3 := by
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) h
  rw [Nat.odd_iff] at hn
  interval_cases n <;> omega

theorem coprime_of_odd_of_dvd_sixteen {n m : ℕ} (hn : Odd n) (h : m ∣ 16) : Nat.Coprime n m := by
  have h2 : Nat.Coprime 2 n :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.2 hn)
  have h16 : Nat.Coprime (2 ^ 4) n := Nat.Coprime.pow_left 4 h2
  exact (Nat.Coprime.coprime_dvd_left (by simpa using h) h16).symm

theorem coprime_three_of_dvd_sixteen {m : ℕ} (h : m ∣ 16) : Nat.Coprime 3 m :=
  coprime_of_odd_of_dvd_sixteen (by decide) h

theorem three_rank_of_survivor_cover (hGA : GriessAllModelsStatement)
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (hodd : Odd (Nat.card (Subgroup.center L))) (hgt : 1 < Nat.card (Subgroup.center L))
    (hS : Survivor (L ⧸ Subgroup.center L)) :
    Nat.card (Subgroup.center L) = 3 ∧ CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 2 := by
  have hperf : Group.IsPerfect L := ⟨hL.1⟩
  rcases hS with ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | h | h
  ·
    exfalso
    have h1 := (card_center_dvd_hopfMultiplier hperf (MulEquiv.refl (L ⧸ Subgroup.center L))).trans
      (card_hopfMultiplier_psl2 hGA h)
    have := eq_one_of_odd_of_dvd_four hodd h1
    omega
  ·
    obtain ⟨m, hm16, hMm⟩ := card_hopfMultiplier_psl3 hGA h
    have hdvd : Nat.card (Subgroup.center L) ∣ Nat.gcd 3 (2 ^ f - 1) * m :=
      hMm ▸ card_center_dvd_hopfMultiplier hperf (MulEquiv.refl (L ⧸ Subgroup.center L))
    have hcop : Nat.Coprime (Nat.card (Subgroup.center L)) m := coprime_of_odd_of_dvd_sixteen hodd hm16
    have hZg : Nat.card (Subgroup.center L) ∣ Nat.gcd 3 (2 ^ f - 1) := hcop.dvd_of_dvd_mul_right hdvd
    have hZ3 : Nat.card (Subgroup.center L) ∣ 3 := hZg.trans (Nat.gcd_dvd_left _ _)
    have hZ : Nat.card (Subgroup.center L) = 3 :=
      (Nat.prime_three.eq_one_or_self_of_dvd _ hZ3).resolve_left (by omega)
    have h3 : 3 ∣ 2 ^ f - 1 := by
      have h3g : 3 ∣ Nat.gcd 3 (2 ^ f - 1) := hZ ▸ hZg
      exact h3g.trans (Nat.gcd_dvd_right _ _)
    refine ⟨hZ, ?_⟩
    obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
    have hf1 : 1 ≤ f := hadm.2.1
    haveI : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1 hK
    have h3K : 3 ∣ Nat.card K - 1 := by
      rw [hK]
      exact h3
    have hM : Nat.card (hopfMultiplier (L ⧸ Subgroup.center L)) = 3 * m := by
      rw [hMm, Nat.gcd_eq_left h3]
    exact pRank_three_le_two_of_psl3_cover hperf e hZ h3K (coprime_three_of_dvd_sixteen hm16) hM
  ·
    have hMm := card_hopfMultiplier_psu3 hGA h
    have hdvd : Nat.card (Subgroup.center L) ∣ Nat.gcd 3 (2 ^ f + 1) :=
      hMm ▸ card_center_dvd_hopfMultiplier hperf (MulEquiv.refl (L ⧸ Subgroup.center L))
    have hZ3 : Nat.card (Subgroup.center L) ∣ 3 := hdvd.trans (Nat.gcd_dvd_left _ _)
    have hZ : Nat.card (Subgroup.center L) = 3 :=
      (Nat.prime_three.eq_one_or_self_of_dvd _ hZ3).resolve_left (by omega)
    have h3 : 3 ∣ 2 ^ f + 1 := by
      have h3g : 3 ∣ Nat.gcd 3 (2 ^ f + 1) := hZ ▸ hdvd
      exact h3g.trans (Nat.gcd_dvd_right _ _)
    refine ⟨hZ, ?_⟩
    obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
    have hf2 : 2 ≤ f := by
      by_contra hlt
      have hf1 : f = 1 := by
        have := hadm.2.1
        omega
      subst hf1
      exact hadm.2.2.2 (by norm_num)
    have hM : Nat.card (hopfMultiplier (L ⧸ Subgroup.center L)) = 3 * 1 := by
      rw [hMm, Nat.gcd_eq_left h3]
    exact pRank_three_le_two_of_psu3_cover hperf hf2 hK e hZ h3 (Nat.coprime_one_right 3) hM
  ·
    exfalso
    have h1 := (card_center_dvd_hopfMultiplier hperf (MulEquiv.refl (L ⧸ Subgroup.center L))).trans
      (card_hopfMultiplier_psp2 hGA h)
    have := eq_one_of_odd_of_dvd_four hodd (h1.trans (by norm_num))
    omega
  ·
    exfalso
    obtain ⟨e⟩ := h
    have h1 := card_center_dvd_hopfMultiplier hperf e
    rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five).2] at h1
    have := eq_one_of_odd_of_dvd_four hodd (h1.trans (by norm_num))
    omega
  ·
    obtain ⟨e⟩ := h
    have h1 := card_center_dvd_hopfMultiplier hperf e
    rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six).2] at h1
    have hZ : Nat.card (Subgroup.center L) = 3 := eq_three_of_odd_of_dvd_six hodd h1 hgt
    refine ⟨hZ, ?_⟩
    have hhat : IsHat L (alternatingGroup (Fin 6)) := ⟨isQuasisimple_of_open hL, hZ, ⟨e⟩⟩
    exact (pRank_three_hatA6 hhat).le

theorem stronglyQuasithin_of_survivor_cover (hGA : GriessAllModelsStatement)
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (hodd : Odd (Nat.card (Subgroup.center L))) (hgt : 1 < Nat.card (Subgroup.center L))
    (hS : Survivor (L ⧸ Subgroup.center L)) : CFSG.Open.SQTKTauCeti.StronglyQuasithin L := by
  obtain ⟨hZ, h3⟩ := three_rank_of_survivor_cover hGA hL hodd hgt hS
  intro p hp hp2
  by_cases hp3 : p = 3
  · subst hp3
    exact h3
  · haveI : Fact p.Prime := ⟨hp⟩
    have hN : ¬ p ∣ Nat.card (Subgroup.center L) := by
      rw [hZ]
      intro hd
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd)
    rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center L) hN]
    exact pRank_le_two_of_survivor hS hp hp2

end CFSG.Quasithin.B69K.OddCovers

end
