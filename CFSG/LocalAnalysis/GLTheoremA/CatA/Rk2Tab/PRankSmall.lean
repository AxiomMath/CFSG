module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

theorem pRank_eq_zero_of_not_dvd_card {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {H : Subgroup G} (hH : ¬ p ∣ Nat.card H) : CFSG.Open.pRank p H = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  refine CFSG.SectionRank.pRank_le hp.one_lt (fun E hEH hE => ?_)
  rw [pow_zero]
  haveI : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p ↥E := hE.isPGroup
  have hdvd : Nat.card E ∣ Nat.card H := Subgroup.card_dvd_of_le hEH
  rcases hEp.card_eq_or_dvd with h | h
  · omega
  · exact absurd (dvd_trans h hdvd) hH

theorem pRank_le_one_of_card_dvd_prime {G : Type*} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) {H : Subgroup G} (h : Nat.card H ∣ q) :
    CFSG.Open.pRank p H ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt (k := 1) fun E hEH hE => ?_
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
  have hdvd2 : p ^ k ∣ q := by rw [← hk]; exact (Subgroup.card_dvd_of_le hEH).trans h
  rw [hk]
  rcases (Nat.dvd_prime hq).1 hdvd2 with h1 | h1
  · rw [h1, pow_one]
    exact hp.one_lt.le
  · have hkp : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at h1
      exact hq.ne_one h1.symm
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1 (h1 ▸ dvd_pow_self p hkp)
    rw [h1, hpq, pow_one]

end CFSG.LocalAnalysis.GLTheoremA
