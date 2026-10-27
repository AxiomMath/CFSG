module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112T1Defs
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112Split
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def SporadicCoverRankTwo : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → SporCentralQuotient L →
    Nat.card (Subgroup.center L) = 3 → CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 →
      CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤ 2

theorem pRank_mulAut_le_of_outer_le_two {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (hout : Nat.card (Outer S) ≤ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) ≤ CFSG.Open.pRank p (⊤ : Subgroup S) := by
  obtain ⟨D, -, hD, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (MulAut S))
  have hcop : Nat.Coprime p (Nat.card (Outer S)) :=
    coprime_of_le_two hp hp2 Nat.card_pos.ne' hout
  have hDp : IsPGroup p D := fun d => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hD.2 d d.2)⟩
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_of_le_inner hcen (le_inner_of_isPGroup hcop hDp) hD
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hE (hEc.trans hcard)

theorem pRank_mulAut_le_centerQuotient_of_outer {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hout : Nat.card (Outer (L ⧸ Subgroup.center L)) ≤ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) :=
  (pRank_mulAut_le_of_quasisimple hp.one_lt hq).trans
    (pRank_mulAut_le_of_outer_le_two hp hp2 (center_quotient_eq_bot_of_quasisimple hq) hout)

theorem card_outer_centerQuotient_le_two (hOut : SporadicOuterLeTwo) {L : Type} [Group L]
    [Finite L] (hq : CFSG.Open.IsQuasisimple L) (hF : SporCentralQuotient L) :
    Nat.card (Outer (L ⧸ Subgroup.center L)) ≤ 2 := by
  obtain ⟨name, he⟩ := hF
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  exact hOut (L ⧸ Subgroup.center L) ‹_› (exists_noncomm_quotient_center_of_quasisimple hq) name he

theorem card_center_dvd_twelve_of_spor (hSpM : Tables.Multiplier.SporadicMultipliers) {L : Type}
    [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L) (hF : SporCentralQuotient L) :
    Nat.card (Subgroup.center L) ∣ 12 := by
  obtain ⟨name, ⟨e⟩⟩ := hF
  exact Tables.Multiplier.card_center_dvd_twelve hSpM hq name e

theorem eq_three_of_dvd_of_dvd_twelve {n p : ℕ} (hn : n ∣ 12) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ n) : p = 3 ∧ ¬ 9 ∣ n := by
  have hp12 : p ∣ 12 := hpn.trans hn
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp12
  refine ⟨?_, fun h9 => absurd (h9.trans hn) (by norm_num)⟩
  interval_cases p <;> simp_all <;> norm_num at hp

theorem pRank_center_le_one_of_dvd_twelve {L : Type} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h12 : Nat.card (Subgroup.center L) ∣ 12) :
    CFSG.Open.pRank p (Subgroup.center L) ≤ 1 := by
  by_contra hk
  push Not at hk
  obtain ⟨E, hEZ, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center L)
  have h1 : p ^ 2 ∣ Nat.card (Subgroup.center L) := by
    refine (pow_dvd_pow p hk).trans ?_
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hEZ
  have hp3 := (eq_three_of_dvd_of_dvd_twelve h12 hp hp2 ((dvd_pow_self p two_ne_zero).trans h1)).1
  subst hp3
  exact absurd (h1.trans h12) (by norm_num)

theorem pRank_eq_zero_of_not_dvd {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {H : Subgroup G} (hH : ¬ p ∣ Nat.card H) : CFSG.Open.pRank p H = 0 := by
  obtain ⟨E, hEH, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  by_contra hk
  apply hH
  have h1 : p ∣ Nat.card E := by rw [hcard]; exact dvd_pow_self p hk
  exact h1.trans (Subgroup.card_dvd_of_le hEH)

theorem tables112On_spor_of (hOut : SporadicOuterLeTwo) (hCov : SporadicCoverRank)
    (hTwo : SporadicCoverRankTwo) (hSpM : Tables.Multiplier.SporadicMultipliers) :
    Tables112On SporCentralQuotient where
  T0 := fun L _ _ _ hq hK => table112_T0 L hq hK
  T1a := fun L _ _ hF hq _ p hp hp2 => by
    have h1 := pRank_mulAut_le_centerQuotient_of_outer hq hp hp2
      (card_outer_centerQuotient_le_two hOut hq hF)
    by_cases hZ : p ∣ Nat.card (Subgroup.center L)
    · have := hCov L hq hF p hp hp2 hZ
      omega
    · have := pRank_centerQuotient_le_of_not_dvd hp hZ
      omega
  T1b := fun L _ _ hF hq _ p hp hp2 _ => by
    have h1 := pRank_mulAut_le_centerQuotient_of_outer hq hp hp2
      (card_outer_centerQuotient_le_two hOut hq hF)
    by_cases hZ : p ∣ Nat.card (Subgroup.center L)
    · have := hCov L hq hF p hp hp2 hZ
      omega
    · have := pRank_centerQuotient_le_of_not_dvd hp hZ
      omega
  T2 := fun L _ _ hF hq _ p hp hp2 => by
    have h12 := card_center_dvd_twelve_of_spor hSpM hq hF
    have h1 := pRank_center_le_one_of_dvd_twelve hp hp2 h12
    by_cases hZ : p ∣ Nat.card (Subgroup.center L)
    · have : Group.IsPerfect L := ⟨hq.1⟩
      have : Fact p.Prime := ⟨hp⟩
      have hpL : p ∣ Nat.card L := hZ.trans (Subgroup.card_subgroup_dvd_card _)
      have h2 := (CFSG.SectionRank.perfect_cyclic_center_odd_elements (L := L) hp2 hpL).2 hZ
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
      omega
    · have := pRank_eq_zero_of_not_dvd hp hZ
      omega
  T3 := fun L _ _ hF hq _ p hp hp2 hZp hZ1 => by
    left
    have h12 := card_center_dvd_twelve_of_spor hSpM hq hF
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZp
    have hk1 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      have := pRank_eq_zero_of_not_dvd hp (H := Subgroup.center L)
        (by rw [hk]; exact hp.not_dvd_one)
      omega
    have hpZ : p ∣ Nat.card (Subgroup.center L) := by rw [hk]; exact dvd_pow_self p hk1
    obtain ⟨hp3, h9⟩ := eq_three_of_dvd_of_dvd_twelve h12 hp hp2 hpZ
    subst hp3
    refine ⟨rfl, ?_⟩
    have hk' : k = 1 := by
      by_contra hne
      apply h9
      rw [hk]
      exact (pow_dvd_pow 3 (by omega : 2 ≤ k))
    rw [hk, hk', pow_one]
  T11 := fun L _ _ hF hq _ p hp hp2 _ h2 => by
    exfalso
    have := pRank_center_le_one_of_dvd_twelve hp hp2 (card_center_dvd_twelve_of_spor hSpM hq hF)
    omega
  T9 := fun L _ _ hF hq _ hZ1 hm2 _ => by
    have h1 := pRank_mulAut_le_centerQuotient_of_outer hq Nat.prime_three (by norm_num)
      (card_outer_centerQuotient_le_two hOut hq hF)
    have hZ : ¬ 3 ∣ Nat.card (Subgroup.center L) := by rw [hZ1]; norm_num
    have := pRank_centerQuotient_le_of_not_dvd Nat.prime_three hZ
    omega
  TFA_a := fun L _ _ hF hq _ hZ1 hm1 _ H hH hcard => by
    exfalso
    have h1 := pRank_mulAut_le_centerQuotient_of_outer hq Nat.prime_three (by norm_num)
      (card_outer_centerQuotient_le_two hOut hq hF)
    have hZ : ¬ 3 ∣ Nat.card (Subgroup.center L) := by rw [hZ1]; norm_num
    have h2 := pRank_centerQuotient_le_of_not_dvd Nat.prime_three hZ
    have h3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut L)) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hH (by rw [hcard]; norm_num)
    omega
  TFA_b := fun L _ _ hF hq _ hZ3 hm2 _ H hH hcard => by
    exfalso
    have h1 := pRank_mulAut_le_centerQuotient_of_outer hq Nat.prime_three (by norm_num)
      (card_outer_centerQuotient_le_two hOut hq hF)
    have h2 := hTwo L hq hF hZ3 hm2
    have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut L)) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hH (by rw [hcard]; norm_num)
    omega

end CFSG.HardMathSupport.Timmesfeld.Coordinator
