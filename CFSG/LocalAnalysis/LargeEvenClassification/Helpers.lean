module

public import CFSG.Mathlib.GroupTheory.Basic
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem rank_exponent_le_card {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime exponent : ℕ} (hprime : 1 < prime)
    (Elementary : Subgroup Ambient) (hcard : Nat.card Elementary = prime ^ exponent) :
    exponent ≤ Nat.card Ambient := by
  exact le_trans (Nat.le_of_lt (Nat.lt_pow_self hprime))
    (hcard ▸ Elementary.card_le_card_group)

theorem pRank_le_card {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) (Local : Subgroup Ambient) :
    pRank prime Local ≤ Nat.card Ambient := CFSG.SectionRank.pRank_le_card_of_one_lt hprime Local

theorem pRank_witness {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) (Local : Subgroup Ambient) :
    ∃ Elementary : Subgroup Ambient,
      Elementary ≤ Local ∧ IsElemAbelian prime Elementary ∧
        Nat.card Elementary = prime ^ pRank prime Local :=
  CFSG.SectionRank.exists_pRank hprime Local

theorem evenRank_le_card (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient] :
    evenRank Ambient ≤ Nat.card Ambient := by
  apply csSup_le'
  rintro rank ⟨prime, Local, hprime, _, _, hrank⟩
  rw [← hrank]
  exact pRank_le_card hprime.one_lt Local

theorem evenRank_witness (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient]
    (hpositive : 0 < evenRank Ambient) :
    ∃ (prime : ℕ) (Local : Subgroup Ambient),
      prime.Prime ∧ prime ≠ 2 ∧ IsTwoLocal Local ∧ pRank prime Local = evenRank Ambient := by
  change evenRank Ambient ∈ {rank | ∃ (prime : ℕ) (Local : Subgroup Ambient),
    prime.Prime ∧ prime ≠ 2 ∧ IsTwoLocal Local ∧ pRank prime Local = rank}
  unfold evenRank
  apply Nat.sSup_mem
  · by_contra hempty
    have hset : {rank | ∃ (prime : ℕ) (Local : Subgroup Ambient),
        prime.Prime ∧ prime ≠ 2 ∧ IsTwoLocal Local ∧ pRank prime Local = rank} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hempty
    have hzero : evenRank Ambient = 0 := by
      unfold evenRank
      rw [hset]
      simp
    omega
  · refine ⟨Nat.card Ambient, ?_⟩
    rintro rank ⟨prime, Local, hprime, _, _, hrank⟩
    rw [← hrank]
    exact pRank_le_card hprime.one_lt Local

theorem evenRank_four_witness (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] (hrank : 4 ≤ evenRank Ambient) :
    ∃ (prime : ℕ) (Local Elementary : Subgroup Ambient),
      prime.Prime ∧ prime ≠ 2 ∧ IsTwoLocal Local ∧ Elementary ≤ Local ∧
        IsElemAbelian prime Elementary ∧
        Nat.card Elementary = prime ^ evenRank Ambient := by
  obtain ⟨prime, Local, hprime, hodd, hlocal, hlocalRank⟩ :=
    evenRank_witness Ambient (by omega)
  obtain ⟨Elementary, hle, helementary, hcard⟩ := pRank_witness hprime.one_lt Local
  exact ⟨prime, Local, Elementary, hprime, hodd, hlocal, hle, helementary,
    hlocalRank ▸ hcard⟩

theorem not_isPGroup_of_nonabelian_simple (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] [IsSimpleGroup Ambient] {prime : ℕ} (hprime : prime.Prime)
    (hnonab : ∃ first second : Ambient, first * second ≠ second * first) :
    ¬ IsPGroup prime Ambient := by
  intro hpgroup
  let : Fact prime.Prime := ⟨hprime⟩
  let : Group.IsNilpotent Ambient := hpgroup.isNilpotent
  let : CommGroup Ambient := instCommGroupOfIsSimpleGroupOfIsNilpotent
  obtain ⟨first, second, hne⟩ := hnonab
  exact hne (mul_comm first second)

theorem twoLocal_ne_top (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient]
    [IsSimpleGroup Ambient]
    (hnonab : ∃ first second : Ambient, first * second ≠ second * first)
    (Local : Subgroup Ambient) (hlocal : IsTwoLocal Local) : Local ≠ ⊤ := by
  obtain ⟨TwoSubgroup, hnontrivial, hpgroup, hnormalizer⟩ := hlocal
  intro htop
  have hnormal : TwoSubgroup.Normal := Subgroup.normalizer_eq_top_iff.mp
    (hnormalizer.symm.trans htop)
  rcases CFSG.eq_bot_or_eq_top_of_normal TwoSubgroup hnormal with hbot | hwhole
  · exact hnontrivial hbot
  · have hpambient : IsPGroup 2 Ambient := by
      rw [hwhole] at hpgroup
      exact hpgroup.of_equiv Subgroup.topEquiv
    exact not_isPGroup_of_nonabelian_simple Ambient Nat.prime_two hnonab hpambient

theorem evenRank_four_prime_power_dvd (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] (hrank : 4 ≤ evenRank Ambient) :
    ∃ prime : ℕ, prime.Prime ∧ prime ≠ 2 ∧ prime ^ 4 ∣ Nat.card Ambient := by
  obtain ⟨prime, Local, Elementary, hprime, hodd, _, _, _, hcard⟩ :=
    evenRank_four_witness Ambient hrank
  refine ⟨prime, hprime, hodd, dvd_trans (Nat.pow_dvd_pow prime hrank) ?_⟩
  rw [← hcard]
  exact Elementary.card_subgroup_dvd_card

end CFSG.LargeEvenClassification.Helpers
