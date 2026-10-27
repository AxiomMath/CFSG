module

public import Mathlib
public import CFSG.Open.Defs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ClassicalInvolution.RouteD.TWR

open CFSG.Open

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

theorem padicValNat_ord_form {p q f k m g : ℕ} [Fact p.Prime] (hq : q = p ^ f)
    (hm : ¬ p ∣ m) (hgm : g ∣ m) : padicValNat p (q ^ k * m / g) = f * k := by
  have hp : p.Prime := Fact.out
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  have hmg : ¬ p ∣ m / g := fun h => hm (h.trans (Nat.div_dvd_of_dvd hgm))
  have hmg0 : m / g ≠ 0 := fun h => hmg (h ▸ dvd_zero p)
  have hq0 : q ≠ 0 := by rw [hq]; exact pow_ne_zero _ hp.ne_zero
  rw [Nat.mul_div_assoc _ hgm, padicValNat.mul (pow_ne_zero _ hq0) hmg0,
    padicValNat.eq_zero_of_not_dvd hmg, hq, ← pow_mul, padicValNat.prime_pow]
  ring

theorem not_dvd_pow_sub_one {p q f i : ℕ} [Fact p.Prime] (hq : q = p ^ f) (hf : 0 < f)
    (hi : 0 < i) : ¬ p ∣ q ^ i - 1 := by
  intro h
  have hp : p.Prime := Fact.out
  have h1 : p ∣ q ^ i := by
    rw [hq, ← pow_mul]
    exact dvd_pow_self p (by positivity)
  have h2 : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by rw [hq]; exact pow_pos hp.pos _)
  have h3 : p ∣ q ^ i - (q ^ i - 1) := Nat.dvd_sub h1 h
  rw [show q ^ i - (q ^ i - 1) = 1 by omega] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem not_dvd_pow_add_one {p q f i : ℕ} [Fact p.Prime] (hq : q = p ^ f) (hf : 0 < f)
    (hi : 0 < i) : ¬ p ∣ q ^ i + 1 := by
  intro h
  have hp : p.Prime := Fact.out
  have h1 : p ∣ q ^ i := by
    rw [hq, ← pow_mul]
    exact dvd_pow_self p (by positivity)
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h))

theorem padicValNat_ordA {p q f n : ℕ} [Fact p.Prime] (hq : q = p ^ f) (hf : 0 < f) (hn : 1 ≤ n) :
    padicValNat p (ordA n q) = f * (n * (n + 1) / 2) := by
  have hp : p.Prime := Fact.out
  unfold ordA
  refine padicValNat_ord_form hq ?_ ?_
  · intro h
    obtain ⟨i, hi, hpi⟩ := (Prime.exists_mem_finset_dvd hp.prime h)
    rw [Finset.mem_Icc] at hi
    exact not_dvd_pow_sub_one hq hf (by omega) hpi
  · refine (Nat.gcd_dvd_right _ _).trans ?_
    refine (Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem (fun i => q ^ i - 1)
      (Finset.mem_Icc.mpr ⟨le_refl 2, by omega⟩)))
    simpa using Nat.sub_dvd_pow_sub_pow q 1 2

theorem padicValNat_ordBC {p q f n : ℕ} [Fact p.Prime] (hq : q = p ^ f) (hf : 0 < f) (hn : 1 ≤ n) :
    padicValNat p (ordBC n q) = f * (n * n) := by
  have hp : p.Prime := Fact.out
  unfold ordBC
  refine padicValNat_ord_form hq ?_ ?_
  · intro h
    obtain ⟨i, hi, hpi⟩ := Prime.exists_mem_finset_dvd hp.prime h
    rw [Finset.mem_Icc] at hi
    exact not_dvd_pow_sub_one hq hf (by omega) hpi
  · refine (Nat.gcd_dvd_right _ _).trans ?_
    refine (Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1)
      (Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩)))
    simpa using Nat.sub_dvd_pow_sub_pow q 1 2

theorem padicValNat_ordD {p q f n : ℕ} [Fact p.Prime] (hq : q = p ^ f) (hf : 0 < f) (hn : 1 ≤ n) :
    padicValNat p (ordD n q) = f * (n * (n - 1)) := by
  have hp : p.Prime := Fact.out
  unfold ordD
  rw [mul_assoc]
  refine padicValNat_ord_form hq ?_ ?_
  · intro h
    rcases hp.dvd_mul.mp h with h1 | h1
    · exact not_dvd_pow_sub_one hq hf (by omega) h1
    · obtain ⟨i, hi, hpi⟩ := Prime.exists_mem_finset_dvd hp.prime h1
      rw [Finset.mem_Icc] at hi
      exact not_dvd_pow_sub_one hq hf (by omega) hpi
  · exact (Nat.gcd_dvd_right _ _).trans (Dvd.intro _ rfl)

theorem padicValNat_ordTwistedD {p q f n : ℕ} [Fact p.Prime] (hq : q = p ^ f) (hf : 0 < f)
    (hn : 1 ≤ n) : padicValNat p (ordTwistedD n q) = f * (n * (n - 1)) := by
  have hp : p.Prime := Fact.out
  unfold ordTwistedD
  rw [mul_assoc]
  refine padicValNat_ord_form hq ?_ ?_
  · intro h
    rcases hp.dvd_mul.mp h with h1 | h1
    · exact not_dvd_pow_add_one hq hf (by omega) h1
    · obtain ⟨i, hi, hpi⟩ := Prime.exists_mem_finset_dvd hp.prime h1
      rw [Finset.mem_Icc] at hi
      exact not_dvd_pow_sub_one hq hf (by omega) hpi
  · exact (Nat.gcd_dvd_right _ _).trans (Dvd.intro _ rfl)

theorem padicValNat_ordG2 {p q f : ℕ} [Fact p.Prime] (hq : q = p ^ f) (hf : 0 < f) :
    padicValNat p (ordG2 q) = f * 6 := by
  have hp : p.Prime := Fact.out
  have : ordG2 q = q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) / 1 := by simp [ordG2, mul_assoc]
  rw [this]
  refine padicValNat_ord_form hq ?_ (one_dvd _)
  intro h
  rcases hp.dvd_mul.mp h with h1 | h1
  · exact not_dvd_pow_sub_one hq hf (by omega) h1
  · exact not_dvd_pow_sub_one hq hf (by omega) h1

theorem padicValNat_ordTrialityD4 {p q f : ℕ} [Fact p.Prime] (hq : q = p ^ f) (hf : 0 < f) :
    padicValNat p (ordTrialityD4 q) = f * 12 := by
  have hp : p.Prime := Fact.out
  have : ordTrialityD4 q = q ^ 12 * ((q ^ 8 + q ^ 4 + 1) * ((q ^ 6 - 1) * (q ^ 2 - 1))) / 1 := by
    simp [ordTrialityD4, mul_assoc]
  rw [this]
  refine padicValNat_ord_form hq ?_ (one_dvd _)
  intro h
  rcases hp.dvd_mul.mp h with h1 | h1
  · have h2 : p ∣ q ^ 8 + q ^ 4 := by
      have hdq : p ∣ q := by rw [hq]; exact dvd_pow_self p hf.ne'
      exact dvd_add (dvd_pow hdq (by omega)) (dvd_pow hdq (by omega))
    exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h2).mp h1))
  · rcases hp.dvd_mul.mp h1 with h3 | h3
    · exact not_dvd_pow_sub_one hq hf (by omega) h3
    · exact not_dvd_pow_sub_one hq hf (by omega) h3

theorem ordD_four_eq (q : ℕ) : ordD 4 q =
    q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * ((q ^ 4 - 1) * (q ^ 6 - 1))) / Nat.gcd 4 (q ^ 4 - 1) := by
  unfold ordD
  have : Finset.Icc 1 (4 - 1) = ({1, 2, 3} : Finset ℕ) := by decide
  rw [this]
  simp [Finset.prod_insert, mul_assoc]

theorem ordD_four_lt (q : ℕ) (hq : 2 ≤ q) : ordD 4 q < ordTrialityD4 q := by
  rw [ordD_four_eq]
  refine lt_of_le_of_lt (Nat.div_le_self _ _) ?_
  have h2 : 0 < q ^ 2 - 1 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have h6 : 0 < q ^ 6 - 1 := by
    have : 2 ≤ q ^ 6 := le_trans hq (Nat.le_self_pow (by norm_num) q)
    omega
  have hA : 0 < q ^ 12 * ((q ^ 2 - 1) * (q ^ 6 - 1)) := by positivity
  have e1 : q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * ((q ^ 4 - 1) * (q ^ 6 - 1))) =
      (q ^ 12 * ((q ^ 2 - 1) * (q ^ 6 - 1))) * ((q ^ 4 - 1) * (q ^ 4 - 1)) := by ring
  have e2 : ordTrialityD4 q = (q ^ 12 * ((q ^ 2 - 1) * (q ^ 6 - 1))) * (q ^ 8 + q ^ 4 + 1) := by
    unfold ordTrialityD4; ring
  rw [e1, e2]
  refine Nat.mul_lt_mul_of_pos_left ?_ hA
  have h4 : q ^ 4 - 1 ≤ q ^ 4 := Nat.sub_le _ _
  calc (q ^ 4 - 1) * (q ^ 4 - 1) ≤ q ^ 4 * q ^ 4 := Nat.mul_le_mul h4 h4
    _ = q ^ 8 := by ring
    _ < q ^ 8 + q ^ 4 + 1 := by omega

theorem toNat_sq_sub (q : ℕ) (hq : 1 ≤ q) : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
  have h : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h]; ring
  rw [this, Int.toNat_natCast]

theorem toNat_cube_sub (q : ℕ) : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = q ^ 3 + 1 := by
  have : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [this, Int.toNat_natCast]

theorem toNat_fourth_sub (q : ℕ) (hq : 1 ≤ q) : ((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4).toNat = q ^ 4 - 1 := by
  have h : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have : ((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4) = ((q ^ 4 - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h]; ring
  rw [this, Int.toNat_natCast]

theorem ordTwistedA_three_eq (q : ℕ) (hq : 1 ≤ q) : ordTwistedA 3 q =
    q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) / Nat.gcd 4 (q + 1) := by
  unfold ordTwistedA
  have : Finset.Icc 2 (3 + 1) = ({2, 3, 4} : Finset ℕ) := by decide
  rw [this, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, toNat_sq_sub q hq, toNat_cube_sub q, toNat_fourth_sub q hq]

theorem not_dvd_toNat {p q f i : ℕ} [Fact p.Prime] (hq : q = p ^ f) (hf : 0 < f) (hi : 0 < i) :
    ¬ p ∣ ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
  intro h
  have hp : p.Prime := Fact.out
  have hdq : (p : ℤ) ∣ (q : ℤ) ^ i := by
    have : p ∣ q ^ i := by
      rw [hq, ← pow_mul]
      exact dvd_pow_self p (by positivity)
    exact_mod_cast this
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ hp.pos
  have hnn : 0 ≤ (q : ℤ) ^ i - (-1 : ℤ) ^ i := by
    have h1 : (1 : ℤ) ≤ (q : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast hq1)
    have h2 : (-1 : ℤ) ^ i ≤ 1 := by
      rcases neg_one_pow_eq_or ℤ i with h | h <;> simp [h]
    linarith
  have hd : (p : ℤ) ∣ (q : ℤ) ^ i - (-1 : ℤ) ^ i := by
    rw [← Int.toNat_of_nonneg hnn]
    exact_mod_cast h
  have h1 : (p : ℤ) ∣ (-1 : ℤ) ^ i := by
    have := dvd_sub hdq hd
    simpa using this
  have h2 : (p : ℤ) ∣ 1 := by
    rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] at h1 <;> simpa using h1
  have h3 : (p : ℤ) = 1 := by
    have := Int.eq_one_of_dvd_one (by positivity) h2
    exact this
  exact hp.one_lt.ne' (by exact_mod_cast h3)

theorem padicValNat_ordTwistedA {p q f n : ℕ} [Fact p.Prime] (hq : q = p ^ f) (hf : 0 < f)
    (hn : 1 ≤ n) : padicValNat p (ordTwistedA n q) = f * (n * (n + 1) / 2) := by
  have hp : p.Prime := Fact.out
  unfold ordTwistedA
  refine padicValNat_ord_form hq ?_ ?_
  · intro h
    obtain ⟨i, hi, hpi⟩ := Prime.exists_mem_finset_dvd hp.prime h
    rw [Finset.mem_Icc] at hi
    exact not_dvd_toNat hq hf (by omega) hpi
  · refine (Nat.gcd_dvd_right _ _).trans ?_
    have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ hp.pos
    refine (Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem
      (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
      (Finset.mem_Icc.mpr ⟨le_refl 2, by omega⟩)))
    show q + 1 ∣ ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat
    rw [toNat_sq_sub q hq1]
    exact Dvd.intro _ (by simpa using (Nat.sq_sub_sq q 1).symm)

theorem v_ordA2 {p f : ℕ} [Fact p.Prime] (hf : 0 < f) :
    padicValNat p (ordA 2 (p ^ f)) = f * 3 := by
  rw [padicValNat_ordA rfl hf (by norm_num)]

theorem v_ordTA2 {p f : ℕ} [Fact p.Prime] (hf : 0 < f) :
    padicValNat p (ordTwistedA 2 (p ^ f)) = f * 3 := by
  rw [padicValNat_ordTwistedA rfl hf (by norm_num)]

theorem v_ordBC2 {p f : ℕ} [Fact p.Prime] (hf : 0 < f) :
    padicValNat p (ordBC 2 (p ^ f)) = f * 4 := by
  rw [padicValNat_ordBC rfl hf (by norm_num)]

end CFSG.ClassicalInvolution.RouteD.TWR
