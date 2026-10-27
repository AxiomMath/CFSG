module

public import CFSG.LocalAnalysis.LargeEvenClassification.Helpers
import CFSG.LocalAnalysis.SectionRank.PRank

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

@[expose] noncomputable def twoLocalPRank (prime : ℕ) (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] : ℕ :=
  twoLocalPrimeRank prime Ambient

@[expose] def oddLocalPrimes (threshold : ℕ) (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] : Set ℕ :=
  {prime | prime.Prime ∧ prime ≠ 2 ∧ prime ∣ Nat.card Ambient ∧
    threshold ≤ twoLocalPRank prime Ambient}

theorem pRank_mono {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) {Small Large : Subgroup Ambient} (hle : Small ≤ Large) :
    pRank prime Small ≤ pRank prime Large := CFSG.SectionRank.pRank_mono hprime hle

theorem pRank_pos_prime_dvd {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (Local : Subgroup Ambient)
    (hrank : 0 < pRank prime Local) : prime ∣ Nat.card Ambient := by
  obtain ⟨Elementary, _, _, hcard⟩ := pRank_witness hprime.one_lt Local
  have hpower : prime ∣ prime ^ pRank prime Local := by
    simpa using Nat.pow_dvd_pow prime hrank
  exact dvd_trans (hcard ▸ hpower) Elementary.card_subgroup_dvd_card

theorem twoLocalPRank_le_pRank {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) :
    twoLocalPRank prime Ambient ≤ pRank prime (⊤ : Subgroup Ambient) := by
  apply csSup_le'
  rintro rank ⟨Local, _, hrank⟩
  rw [← hrank]
  exact pRank_mono hprime le_top

theorem twoLocalPRank_le_card {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) : twoLocalPRank prime Ambient ≤ Nat.card Ambient := by
  exact (twoLocalPRank_le_pRank hprime).trans (pRank_le_card hprime ⊤)

theorem pRank_le_twoLocalPRank {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) (Local : Subgroup Ambient) (hlocal : IsTwoLocal Local) :
    pRank prime Local ≤ twoLocalPRank prime Ambient := by
  apply le_csSup
  · refine ⟨Nat.card Ambient, ?_⟩
    rintro rank ⟨OtherLocal, _, hrank⟩
    rw [← hrank]
    exact pRank_le_card hprime OtherLocal
  · exact ⟨Local, hlocal, rfl⟩

theorem twoLocalPRank_le_evenRank {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (hodd : prime ≠ 2) :
    twoLocalPRank prime Ambient ≤ evenRank Ambient := by
  apply csSup_le_csSup'
  · refine ⟨Nat.card Ambient, ?_⟩
    rintro rank ⟨otherPrime, Local, hotherPrime, _, _, hrank⟩
    rw [← hrank]
    exact pRank_le_card hotherPrime.one_lt Local
  · rintro rank ⟨Local, hlocal, hrank⟩
    exact ⟨prime, Local, hprime, hodd, hlocal, hrank⟩

theorem twoLocalPRank_pos_witness {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : 1 < prime)
    (hrank : 0 < twoLocalPRank prime Ambient) :
    ∃ Local : Subgroup Ambient, IsTwoLocal Local ∧
      pRank prime Local = twoLocalPRank prime Ambient := by
  change twoLocalPRank prime Ambient ∈
    {rank | ∃ Local : Subgroup Ambient, IsTwoLocal Local ∧ pRank prime Local = rank}
  unfold twoLocalPRank CFSG.Open.twoLocalPrimeRank
  apply Nat.sSup_mem
  · by_contra hempty
    have hset : {rank | ∃ Local : Subgroup Ambient,
        IsTwoLocal Local ∧ pRank prime Local = rank} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hempty
    have hzero : twoLocalPRank prime Ambient = 0 := by
      unfold twoLocalPRank CFSG.Open.twoLocalPrimeRank
      rw [hset]
      simp
    omega
  · refine ⟨Nat.card Ambient, ?_⟩
    rintro rank ⟨Local, _, hlocalRank⟩
    rw [← hlocalRank]
    exact pRank_le_card hprime Local

theorem twoLocalPRank_pos_prime_dvd {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime)
    (hrank : 0 < twoLocalPRank prime Ambient) : prime ∣ Nat.card Ambient := by
  obtain ⟨Local, _, hlocalRank⟩ := twoLocalPRank_pos_witness hprime.one_lt hrank
  exact pRank_pos_prime_dvd hprime Local (hlocalRank ▸ hrank)

theorem oddLocalPrimes_nonempty_iff {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {threshold : ℕ} (hthreshold : 0 < threshold) :
    (oddLocalPrimes threshold Ambient).Nonempty ↔ threshold ≤ evenRank Ambient := by
  constructor
  · rintro ⟨prime, hprime, hodd, _, hrank⟩
    exact hrank.trans (twoLocalPRank_le_evenRank hprime hodd)
  · intro hrank
    obtain ⟨prime, Local, hprime, hodd, hlocal, hlocalRank⟩ :=
      evenRank_witness Ambient (hthreshold.trans_le hrank)
    have hlocalPositive : 0 < pRank prime Local := hlocalRank ▸ hthreshold.trans_le hrank
    refine ⟨prime, hprime, hodd, pRank_pos_prime_dvd hprime Local hlocalPositive, ?_⟩
    exact (hlocalRank ▸ hrank).trans (pRank_le_twoLocalPRank hprime.one_lt Local hlocal)

theorem oddLocalPrimes_antitone {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {smallThreshold largeThreshold : ℕ} (hle : smallThreshold ≤ largeThreshold) :
    oddLocalPrimes largeThreshold Ambient ⊆ oddLocalPrimes smallThreshold Ambient := by
  rintro prime ⟨hprime, hodd, hdivides, hrank⟩
  exact ⟨hprime, hodd, hdivides, hle.trans hrank⟩

theorem oddLocalPrimes_above_evenRank (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] : oddLocalPrimes (evenRank Ambient + 1) Ambient = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro prime ⟨hprime, hodd, _, hrank⟩
  have hbound := twoLocalPRank_le_evenRank (Ambient := Ambient) hprime hodd
  omega

theorem oddLocalPrimes_finite (threshold : ℕ) (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] : (oddLocalPrimes threshold Ambient).Finite := by
  apply (Set.finite_Iic (Nat.card Ambient)).subset
  rintro prime ⟨_, _, hdivides, _⟩
  exact Nat.le_of_dvd Nat.card_pos hdivides

end CFSG.LargeEvenClassification.Helpers
