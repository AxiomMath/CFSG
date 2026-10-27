module

public import CFSG.CharacterTheory.Wreathed.CentralSylowPowerQuotients

public section

namespace CFSG.Wreathed.ConditionalFourier

open CFSG.Wreathed

variable {G : Type} [Group G]

theorem eq_half_power_of_orderOf_eq_two {a y : G} {n : ℕ} (hn : 1 ≤ n) (ha : orderOf a = 2 ^ n)
    (hy : y ∈ Subgroup.zpowers a) (hy2 : orderOf y = 2) : y = a ^ (2 ^ n / 2) := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hsq : a ^ (2 * i) = 1 := by
    rw [mul_comm, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, ← hy2,
      pow_orderOf_eq_one]
  have hdvd : ((2 ^ n : ℕ) : ℤ) ∣ 2 * i := by
    rw [← ha]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hsq
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hhalf : 2 ^ (m + 1) / 2 = 2 ^ m := by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  rw [hhalf]
  have hdvd' : ((2 ^ m : ℕ) : ℤ) ∣ i := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c, ?_⟩
    push_cast at hc ⊢
    rw [pow_succ] at hc
    linarith
  obtain ⟨t, rfl⟩ := hdvd'
  rcases Int.even_or_odd t with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exfalso
    have h1 : a ^ (((2 ^ m : ℕ) : ℤ) * (s + s)) = 1 := by
      rw [show ((2 ^ m : ℕ) : ℤ) * (s + s) = ((2 ^ (m + 1) : ℕ) : ℤ) * s by push_cast; ring,
        zpow_mul, zpow_natCast, ← ha, pow_orderOf_eq_one, one_zpow]
    rw [h1, orderOf_one] at hy2
    norm_num at hy2
  · have hexp : ((2 ^ m : ℕ) : ℤ) * (2 * s + 1) =
        ((2 ^ (m + 1) : ℕ) : ℤ) * s + ((2 ^ m : ℕ) : ℤ) := by push_cast; ring
    rw [hexp, zpow_add, zpow_mul, zpow_natCast, zpow_natCast, ← ha, pow_orderOf_eq_one,
      one_zpow, one_mul]

theorem wreath_powers_eq_of_isConj [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) {k h : ℕ} (hk : k ∈ Finset.Ico 1 (2 ^ n))
    (hh : h ∈ Finset.Ico 1 (2 ^ n))
    (hconj : IsConj (wreathModelHom S e (Original.a (2 ^ n)) ^ k)
      (wreathModelHom S e (Original.a (2 ^ n)) ^ h)) : k = h := by
  rw [Finset.mem_Ico] at hk hh
  have hk' : ¬ ((2 ^ n : ℕ) : ℤ) ∣ (k : ℤ) := fun hd => by
    have h1 := Int.le_of_dvd (by omega) hd
    have h2 : 2 ^ n ≤ k := by exact_mod_cast h1
    omega
  obtain ⟨c, hc⟩ := exists_zpow_eq_involution n (by omega) S e (k : ℤ) hk'
  rw [zpow_natCast] at hc
  set a := wreathModelHom S e (Original.a (2 ^ n)) with ha_def
  have ha : orderOf a = 2 ^ n := orderOf_wreathModelHom_a n S e
  set x := wreathModelHom S e (Original.x (2 ^ n)) with hx_def
  have hxa : x = a ^ (2 ^ n / 2) := wreathModelHom_x_eq n S e
  have hxord : orderOf x = 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hhalf : 2 ^ (m + 1) / 2 = 2 ^ m := by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hdvd : 2 ^ m ∣ orderOf a := ⟨2, by rw [ha, pow_succ]⟩
    rw [hxa, hhalf, orderOf_pow_of_dvd (by positivity) hdvd, ha, pow_succ,
      Nat.mul_div_cancel_left _ (by positivity)]
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hgx : g * x * g⁻¹ = x := by
    have hconjx : g * x * g⁻¹ = (a ^ h) ^ c := by
      rw [← hc, ← hg, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [hconjx]
    have hord : orderOf ((a ^ h) ^ c) = 2 := by
      rw [← hconjx, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hxord]
    have hmem : (a ^ h) ^ c ∈ Subgroup.zpowers a :=
      Subgroup.zpow_mem _ (Subgroup.npow_mem_zpowers a h) c
    rw [eq_half_power_of_orderOf_eq_two (by omega) ha hmem hord, ← hxa]
  have hgN : g ∈ involutionCentralizer n S e := by
    change g ∈ Subgroup.centralizer {x}
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [hgx]
  obtain ⟨r, hr, c', hc'C, hgrc⟩ :=
    involutionCentralizer_eq_oddCore_mul_centralSylowPower n hn S e 1 ⟨g, hgN⟩
  have hc'a : (c' : G) * a = a * c' := by
    have h1 := hc'C
    rw [Subgroup.mem_centralizer_singleton_iff, zpow_one] at h1
    exact h1
  have hgval : g = (r : G) * c' := congrArg Subtype.val hgrc
  have hrk : (r : G) * a ^ k * (r : G)⁻¹ = a ^ h := by
    rw [← hg, hgval]
    have hck : (c' : G) * a ^ k * (c' : G)⁻¹ = a ^ k := by
      rw [((Commute.pow_right (show Commute (c' : G) a from hc'a) k).eq), mul_assoc,
        mul_inv_cancel, mul_one]
    calc (r : G) * a ^ k * (r : G)⁻¹ = (r : G) * ((c' : G) * a ^ k * (c' : G)⁻¹) * (r : G)⁻¹ := by
          rw [hck]
      _ = (r : G) * c' * a ^ k * ((r : G) * c')⁻¹ := by group
  have haN : ∀ j : ℕ, a ^ j ∈ involutionCentralizer n S e := by
    intro j
    change a ^ j ∈ Subgroup.centralizer {x}
    rw [Subgroup.mem_centralizer_singleton_iff, hxa]
    exact (Commute.pow_pow_self a _ _).eq
  let A : ℕ → involutionCentralizer n S e := fun j => ⟨a ^ j, haN j⟩
  have hdiff : A h * (A k)⁻¹ ∈ centralizerOddCore n S e := by
    have hR := (centralizerOddCore n S e).mul_mem hr
      ((centralizerOddCore_normal n S e).conj_mem _ (inv_mem hr) (A k))
    have hval : r * (A k * r⁻¹ * (A k)⁻¹) = A h * (A k)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, A]
      rw [← hrk]
      group
    rwa [hval] at hR
  have hodd : Odd (Nat.card (centralizerOddCore n S e)) := centralizerOddCore_card_odd n S e
  have hord1 : orderOf (A h * (A k)⁻¹) = 1 := by
    have h1 : orderOf (A h * (A k)⁻¹) ∣ Nat.card (centralizerOddCore n S e) := by
      have := Subgroup.orderOf_dvd_natCard (centralizerOddCore n S e) hdiff
      exact this
    have h2 : orderOf (A h * (A k)⁻¹) ∣ 2 ^ n := by
      rw [← Subgroup.orderOf_coe, ← ha]
      apply orderOf_dvd_of_mem_zpowers
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, A]
      exact Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers a h)
        (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers a k))
    obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    rw [ht] at h1
    rcases t with _ | t
    · simpa using ht
    · exfalso
      have h3 : 2 ∣ Nat.card (centralizerOddCore n S e) :=
        (dvd_pow_self 2 (Nat.succ_ne_zero t)).trans h1
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)
  rw [orderOf_eq_one_iff] at hord1
  have hakh : a ^ h = a ^ k := by
    have := congrArg Subtype.val hord1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, A] at this
    exact mul_inv_eq_one.mp this
  have := pow_inj_mod.mp hakh
  rw [ha, Nat.mod_eq_of_lt hh.2, Nat.mod_eq_of_lt hk.2] at this
  exact this.symm

end CFSG.Wreathed.ConditionalFourier
