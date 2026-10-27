module

public import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64iiNPC

theorem pow_conj_zpow {G : Type*} [Group G] {y γ : G} {r : ℤ} (h : y * γ * y⁻¹ = γ ^ r)
    (n : ℕ) (s : ℤ) : y ^ n * γ ^ s * (y ^ n)⁻¹ = γ ^ (s * r ^ n) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    have h1 : y ^ (n + 1) * γ ^ s * (y ^ (n + 1))⁻¹ = y * (y ^ n * γ ^ s * (y ^ n)⁻¹) * y⁻¹ := by
      rw [pow_succ', mul_inv_rev]; group
    rw [h1, ih, ← conj_zpow, h, ← zpow_mul, pow_succ']
    congr 1
    ring

theorem exists_sum_pow_eq_mul {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {m : ℤ}
    (hm : (p : ℤ) ∣ m - 1) :
    ∃ n₁ : ℤ, ¬ (p : ℤ) ∣ n₁ ∧ ∑ i ∈ Finset.range p, m ^ i = p * n₁ := by
  obtain ⟨k, hk⟩ := hm
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  obtain ⟨q, hq⟩ := hodd
  have hmod : ((∑ i ∈ Finset.range p, m ^ i : ℤ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) := by
    have hp0 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
      rw [← Nat.cast_pow]
      exact ZMod.natCast_self _
    have hm' : (m : ZMod (p ^ 2)) = 1 + (p : ZMod (p ^ 2)) * k := by
      have : m = 1 + p * k := by linarith
      rw [this]
      push_cast
      ring
    have hpow : ∀ i : ℕ,
        (m : ZMod (p ^ 2)) ^ i = 1 + (i : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * k) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ (m : ZMod (p ^ 2)) i, ih, hm']
        push_cast
        have : ((p : ZMod (p ^ 2)) * k) * ((p : ZMod (p ^ 2)) * k) = 0 := by
          have : ((p : ZMod (p ^ 2)) * k) * ((p : ZMod (p ^ 2)) * k)
              = (p : ZMod (p ^ 2)) ^ 2 * (k : ZMod (p ^ 2)) ^ 2 := by ring
          rw [this, hp0, zero_mul]
        linear_combination (i : ZMod (p ^ 2)) * this
    push_cast
    simp_rw [hpow]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_range]
    have hsum : (∑ i ∈ Finset.range p, ((i : ℕ) : ZMod (p ^ 2))) = (p : ZMod (p ^ 2)) * q := by
      have h2 := Finset.sum_range_id_mul_two p
      have h3 : (∑ i ∈ Finset.range p, i) = p * q := by
        subst hq
        have : (2 * q + 1) * (2 * q + 1 - 1) = (2 * q + 1) * q * 2 := by
          rw [Nat.add_sub_cancel]; ring
        omega
      have := congrArg (fun n : ℕ => (n : ZMod (p ^ 2))) h3
      simpa [Nat.cast_sum] using this
    rw [hsum]
    have : (p : ZMod (p ^ 2)) * q * ((p : ZMod (p ^ 2)) * k)
        = (p : ZMod (p ^ 2)) ^ 2 * ((q : ZMod (p ^ 2)) * k) := by ring
    rw [this, hp0, zero_mul, add_zero]
    simp
  have hmod' : ((∑ i ∈ Finset.range p, m ^ i : ℤ) : ZMod (p ^ 2)) = ((p : ℤ) : ZMod (p ^ 2)) := by
    rw [hmod]
    simp
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub (p : ℤ) (∑ i ∈ Finset.range p, m ^ i) (p ^ 2)).1
    hmod'.symm
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨1 + p * c, ?_, ?_⟩
  · intro h
    have h1 : (p : ℤ) ∣ 1 := by
      have := (dvd_add_left (dvd_mul_right (p : ℤ) c)).1 h
      exact this
    have := Int.eq_one_of_dvd_one (by positivity) h1
    have hp1 := hp.out.one_lt
    omega
  · push_cast at hc
    linear_combination hc

theorem commute_of_pow_prime_pow {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {r w : G}
    (hr : orderOf r = p) (hw : w * r * w⁻¹ ∈ Subgroup.zpowers r) {c : ℕ}
    (hc : w ^ (p ^ c) * r = r * w ^ (p ^ c)) : w * r = r * w := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hw
  have h1 : w ^ (p ^ c) * r ^ (1 : ℤ) * (w ^ (p ^ c))⁻¹ = r ^ ((1 : ℤ) * j ^ (p ^ c)) :=
    pow_conj_zpow hj.symm (p ^ c) 1
  have h2 : w ^ (p ^ c) * r ^ (1 : ℤ) * (w ^ (p ^ c))⁻¹ = r := by
    rw [zpow_one, hc]
    group
  rw [h2, one_mul] at h1
  have h3 : r ^ (j ^ (p ^ c) - 1) = 1 := by
    rw [zpow_sub, zpow_one, ← h1, mul_inv_cancel]
  have h4 : ((p : ℕ) : ℤ) ∣ j ^ (p ^ c) - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h3
    rwa [hr] at this
  have h5 : ((j : ZMod p)) = 1 := by
    have h6 := (ZMod.intCast_zmod_eq_zero_iff_dvd (j ^ (p ^ c) - 1) p).2 h4
    push_cast at h6
    rw [ZMod.pow_card_pow] at h6
    exact sub_eq_zero.1 h6
  have h7 : ((p : ℕ) : ℤ) ∣ j - 1 := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (j - 1) p).1 ?_
    push_cast
    rw [h5, sub_self]
  have h8 : r ^ (j - 1) = 1 := by
    refine orderOf_dvd_iff_zpow_eq_one.1 ?_
    rwa [hr]
  have h9 : w * r * w⁻¹ = r := by
    rw [← hj]
    rw [zpow_sub, zpow_one, mul_inv_eq_one] at h8
    exact h8
  calc w * r = (w * r * w⁻¹) * w := by group
    _ = r * w := by rw [h9]

theorem commute_of_torsion_commute {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {γ y : G}
    {a : ℕ} (hγ : orderOf γ = p ^ a) (hy : y * γ * y⁻¹ ∈ Subgroup.zpowers γ)
    (htor : y * γ ^ (p ^ (a - 1)) * y⁻¹ = γ ^ (p ^ (a - 1)))
    {e : ℕ} (he : ¬ p ∣ e) (hye : y ^ e * γ = γ * y ^ e) : y * γ = γ * y := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have : γ = 1 := by rwa [pow_zero, orderOf_eq_one_iff] at hγ
    subst this
    simp
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hr' : y * γ * y⁻¹ = γ ^ r := hr.symm
  have hpa : ((p ^ a : ℕ) : ℤ) = (p : ℤ) * (p : ℤ) ^ (a - 1) := by
    push_cast
    rw [← pow_succ']
    congr 1
    omega
  have h1 : y ^ 1 * γ ^ (((p ^ (a - 1) : ℕ)) : ℤ) * (y ^ 1)⁻¹
      = γ ^ ((((p ^ (a - 1) : ℕ)) : ℤ) * r ^ 1) := pow_conj_zpow hr' 1 _
  have h2 : γ ^ ((((p ^ (a - 1) : ℕ)) : ℤ) * r ^ 1 - ((p ^ (a - 1) : ℕ) : ℤ)) = 1 := by
    rw [zpow_sub, ← h1]
    simp only [zpow_natCast, pow_one] at htor ⊢
    rw [htor, mul_inv_cancel]
  have h3 : ((p ^ a : ℕ) : ℤ) ∣ (((p ^ (a - 1) : ℕ)) : ℤ) * (r - 1) := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h2
    rw [hγ] at this
    have e1 : (((p ^ (a - 1) : ℕ)) : ℤ) * r ^ 1 - ((p ^ (a - 1) : ℕ) : ℤ)
        = (((p ^ (a - 1) : ℕ)) : ℤ) * (r - 1) := by ring
    rwa [e1] at this
  have h4 : (p : ℤ) ∣ r - 1 := by
    have hp0 : ((p : ℤ) ^ (a - 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    rw [hpa] at h3
    push_cast at h3
    rw [mul_comm ((p : ℤ) ^ (a - 1))] at h3
    exact (mul_dvd_mul_iff_right hp0).1 h3
  have h5 : y ^ e * γ ^ (1 : ℤ) * (y ^ e)⁻¹ = γ ^ ((1 : ℤ) * r ^ e) := pow_conj_zpow hr' e 1
  have h6 : γ ^ (r ^ e - 1) = 1 := by
    rw [zpow_one, hye, mul_inv_cancel_right, one_mul] at h5
    rw [zpow_sub, zpow_one, ← h5, mul_inv_cancel]
  have h7 : ((p ^ a : ℕ) : ℤ) ∣ r ^ e - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h6
    rwa [hγ] at this
  have h8 : ¬ (p : ℤ) ∣ ∑ i ∈ Finset.range e, r ^ i := by
    intro hdvd
    have hr1 : (r : ZMod p) = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (r - 1) p).2 (by exact_mod_cast h4)
      push_cast at this
      exact sub_eq_zero.1 this
    have h9 := (ZMod.intCast_zmod_eq_zero_iff_dvd (∑ i ∈ Finset.range e, r ^ i) p).2
      (by exact_mod_cast hdvd)
    push_cast at h9
    simp [hr1] at h9
    exact he ((ZMod.natCast_eq_zero_iff e p).1 h9)
  have h9 : IsCoprime ((p : ℤ) ^ a) (∑ i ∈ Finset.range e, r ^ i) :=
    IsCoprime.pow_left ((Nat.prime_iff_prime_int.1 hp.out).coprime_iff_not_dvd.2 h8)
  have h10 : ((p : ℤ) ^ a) ∣ r - 1 := by
    have h7' : ((p : ℤ) ^ a) ∣ (∑ i ∈ Finset.range e, r ^ i) * (r - 1) := by
      rw [geom_sum_mul]
      push_cast at h7
      exact h7
    exact h9.dvd_of_dvd_mul_left h7'
  have h11 : γ ^ (r - 1) = 1 := by
    refine orderOf_dvd_iff_zpow_eq_one.1 ?_
    rw [hγ]
    push_cast
    exact h10
  have h12 : y * γ * y⁻¹ = γ := by
    rw [zpow_sub, zpow_one, mul_inv_eq_one] at h11
    rw [hr', h11]
  calc y * γ = (y * γ * y⁻¹) * y := by group
    _ = γ * y := by rw [h12]

theorem inv_mul_mul_mem_zpowers {G : Type*} [Group G] [Finite G] {w r : G}
    (h : w * r * w⁻¹ ∈ Subgroup.zpowers r) : w⁻¹ * r * w ∈ Subgroup.zpowers r := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h
  have hpos : 0 < orderOf w := orderOf_pos w
  have h1 := pow_conj_zpow hj.symm (orderOf w - 1) 1
  have h2 : w ^ (orderOf w - 1) = w⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [h2, zpow_one, inv_inv] at h1
  rw [h1]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers r) _

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64iiNPC
