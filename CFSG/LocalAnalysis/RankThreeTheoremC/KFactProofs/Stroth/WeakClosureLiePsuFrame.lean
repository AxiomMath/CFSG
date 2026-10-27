module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTwistFrame
public import CFSG.GroupTheory.WeirSylow.Unitary
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePsuDescent
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePsuBlock

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.GroupTheory.WeirSylow Module

theorem nonempty_suFrame {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L : Type} [Field L] [Fintype L]
    {q : ℕ} (hq : Fintype.card L = q ^ 2) (hpq : ¬ p ∣ q) (hpq1 : ¬ p ∣ q + 1) (n : ℕ)
    {e a r : ℕ} (he : orderOf (-(q : ZMod p)) = e) (ha : padicValInt p ((-(q : ℤ)) ^ e - 1) = a)
    (hr : n / e = r) :
    ∃ μ : ℤ, ¬ (p : ℤ) ∣ μ - 1 ∧
      Nonempty (TwistFrame (Multiplicative (ZMod (p ^ a))) r (StatedSU n q L) μ) := by
  obtain ⟨f, hqf, h⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData L hq
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · have := Fintype.one_lt_card (α := L)
      rw [hq] at this
      norm_num at this
    · exact hq0
  have hcp : ¬ (p : ℤ) ∣ -(q : ℤ) := by
    rw [dvd_neg]
    exact_mod_cast hpq
  have hord : ordMod p (-(q : ℤ)) = e := (ordMod_neg_natCast q).trans he
  have he0 : 0 < e := by
    rw [← hord]
    exact ordMod_pos hcp
  have he1 : e ≠ 1 := by
    intro h1
    have h2 : (p : ℤ) ∣ (-(q : ℤ)) ^ 1 - 1 :=
      (dvd_pow_sub_one_iff (p := p) (c := -(q : ℤ)) 1).2 (Nat.dvd_one.2 (hord.trans h1))
    apply hpq1
    have h3 : (p : ℤ) ∣ ((q + 1 : ℕ) : ℤ) := by
      have h4 : ((q + 1 : ℕ) : ℤ) = -((-(q : ℤ)) ^ 1 - 1) := by push_cast; ring
      rw [h4]
      exact dvd_neg.2 h2
    exact_mod_cast h3
  have hsq_iff : (p : ℤ) ∣ (q : ℤ) ^ 2 - 1 ↔ e ∣ 2 := by
    have h5 := dvd_pow_sub_one_iff (p := p) (c := -(q : ℤ)) 2
    rwa [neg_sq, hord] at h5
  have hdvdZ : (p : ℤ) ^ a ∣ (-(q : ℤ)) ^ e - 1 := by
    rw [← ha]
    exact padicValInt_dvd _
  have hr' : r * e ≤ n := by
    rw [← hr]
    exact Nat.div_mul_le_self n e
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  rcases Nat.even_or_odd e with hev | hodd
  ·
    obtain ⟨k, rfl⟩ := hev.two_dvd
    have hdvdN : p ^ a ∣ q ^ (2 * k) - 1 := by
      have h1 : (p : ℤ) ^ a ∣ (q : ℤ) ^ (2 * k) - 1 := by
        rwa [Even.neg_pow (even_two_mul k)] at hdvdZ
      have h2 : ((q ^ (2 * k) - 1 : ℕ) : ℤ) = (q : ℤ) ^ (2 * k) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_pow, Nat.cast_one]
      have h3 : (p : ℤ) ^ a ∣ ((q ^ (2 * k) - 1 : ℕ) : ℤ) := by
        rw [h2]
        exact h1
      exact_mod_cast h3
    rcases Nat.lt_or_ge k 2 with hk | hk
    ·
      obtain rfl : k = 1 := by omega
      have hdvd2 : p ^ a ∣ q ^ 2 - 1 := by simpa using hdvdN
      have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        have h6 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
        zify [hq1, h6]
        ring
      have hcop : Nat.Coprime (p ^ a) (q + 1) :=
        Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hpq1)
      have hm2 : p ^ a ∣ q - 1 := hcop.dvd_of_dvd_mul_right (by rw [← hfac]; exact hdvd2)
      have hm1 : ¬ (p : ℤ) ∣ (-1 : ℤ) - 1 := by
        intro hd
        have h7 : (p : ℤ) ∣ 2 := by
          rw [show (-1 : ℤ) - 1 = -2 by norm_num, dvd_neg] at hd
          exact hd
        have h8 : p ∣ 2 := by exact_mod_cast h7
        exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).1 h8)
      obtain ⟨S₀, ρ, J, hS₀, hfin, hρ, hJ, hJdet⟩ := exists_suBlock_two h hq hqf hm2
      refine ⟨-1, hm1, ?_⟩
      refine nonempty_suFrame_of_block hqf hpq1 S₀ hS₀ ρ hρ (μ := -1) J
        (fun c => by rw [zpow_neg_one]; exact hJ c) hJdet ?_
      rw [hfin]
      simpa using hr'
    ·
      have hsq : ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 - 1 := fun hd => by
        have h9 := Nat.le_of_dvd (by norm_num) (hsq_iff.1 hd)
        omega
      obtain ⟨S₀, ρ, φ, hS₀, hfin, hρ, hφ, hφdet⟩ :=
        exists_suBlock_even h hq hqf (k := k) (by omega) hdvdN
      refine ⟨(q : ℤ) ^ 2, hsq, ?_⟩
      refine nonempty_suFrame_of_block hqf hpq1 S₀ hS₀ ρ hρ φ hφ hφdet ?_
      rw [hfin]
      exact hr'
  ·
    have hm : p ^ a ∣ q ^ e + 1 := by
      have h1 := hdvdZ
      rw [Odd.neg_pow hodd, show -(q : ℤ) ^ e - 1 = -((q : ℤ) ^ e + 1) by ring, dvd_neg] at h1
      exact_mod_cast h1
    have hsq : ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 - 1 := fun hd => by
      have h9 := Nat.le_of_dvd (by norm_num) (hsq_iff.1 hd)
      have h10 := Nat.odd_iff.1 hodd
      omega
    obtain ⟨S₀, ρ, φ, z, hS₀, hfin, hρ, hφ, hφdet, -, -⟩ := exists_suBlock_odd h hq hqf hodd hm
    refine ⟨(q : ℤ) ^ 2, hsq, ?_⟩
    refine nonempty_suFrame_of_block hqf hpq1 S₀ hS₀ ρ hρ φ hφ hφdet ?_
    rw [hfin]
    exact hr'

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
