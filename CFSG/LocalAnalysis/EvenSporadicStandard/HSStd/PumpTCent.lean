module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpT

open Subgroup

theorem mem_zpowers_of_central {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x d : G} (hx : orderOf x = p) (hxc : ∀ g : G, g * x = x * g) (hd : d ^ p = 1)
    (hG : ¬ p ^ 2 ∣ Nat.card G) : d ∈ zpowers x := by
  have hxz : x ∈ center G := mem_center_iff.2 hxc
  have hN : (zpowers x).Normal := ⟨fun n hn g => by
    have hnc : n ∈ center G := (zpowers_le.2 hxz) hn
    rw [mem_center_iff.1 hnc g, mul_inv_cancel_right]
    exact hn⟩
  have hcardN : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have hcard : Nat.card G = Nat.card (G ⧸ zpowers x) * p := by
    rw [card_eq_card_quotient_mul_card_subgroup (zpowers x), hcardN]
  have hnd : ¬ p ∣ Nat.card (G ⧸ zpowers x) := by
    rintro ⟨m, hm⟩
    exact hG ⟨m, by rw [hcard, hm]; ring⟩
  have hdq : (QuotientGroup.mk d : G ⧸ zpowers x) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hd, QuotientGroup.mk_one]
  rcases (Nat.dvd_prime hp.out).1 (orderOf_dvd_of_pow_eq_one hdq) with h1 | h1
  · exact (QuotientGroup.eq_one_iff d).1 (orderOf_eq_one_iff.1 h1)
  · exact absurd (h1 ▸ orderOf_dvd_natCard (QuotientGroup.mk d : G ⧸ zpowers x)) hnd

variable {R : Type*} [Group R]

theorem eq_one_of_pow_prime [Finite R] {p : ℕ} [hp : Fact p.Prime] {y x d : R} {k : ℕ}
    (hxy : x = y ^ k) {D : Subgroup R} (hx : orderOf x = p) (hxD : x ∉ D)
    (hDC : D ≤ centralizer ({y} : Set R)) (hC : ¬ p ^ 2 ∣ Nat.card (centralizer ({y} : Set R)))
    (hd : d ∈ D) (hdp : d ^ p = 1) : d = 1 := by
  by_contra hd1
  subst hxy
  have hxC : y ^ k ∈ centralizer ({y} : Set R) :=
    mem_centralizer_singleton_iff.2 ((Commute.refl y).pow_left k).eq
  have hmem : (⟨d, hDC hd⟩ : centralizer ({y} : Set R)) ∈
      zpowers (⟨y ^ k, hxC⟩ : centralizer ({y} : Set R)) := by
    refine mem_zpowers_of_central (p := p) ?_ ?_ ?_ hC
    · rw [Subgroup.orderOf_mk]
      exact hx
    · intro g
      have hg : (g : R) * y = y * (g : R) := mem_centralizer_singleton_iff.1 g.2
      exact Subtype.ext (((Commute.pow_right (show Commute (g : R) y from hg) k)).eq)
    · exact Subtype.ext (by simpa using hdp)
  have hdz : d ∈ zpowers (y ^ k) := by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hmem
    exact mem_zpowers_iff.2 ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hdo : orderOf d = p := orderOf_eq_prime hdp hd1
  have heq : zpowers d = zpowers (y ^ k) := by
    refine eq_of_le_of_card_ge (zpowers_le.2 hdz) (le_of_eq ?_)
    rw [Nat.card_zpowers, Nat.card_zpowers, hdo, hx]
  exact hxD ((zpowers_le.2 hd) (by rw [heq]; exact mem_zpowers _))

theorem card_centralizer_le_two_of_order_fifteen [Finite R] {x5 x3 : R} {S : Set R}
    (hx5 : orderOf x5 = 5) (hx3 : orderOf x3 = 3) (hc : x5 * x3 = x3 * x5)
    (h5S : x5 ∈ S) (h3S : x3 ∈ S) (hn5 : x5 ∉ centralizer S) (hn3 : x3 ∉ centralizer S)
    (hC : Nat.card (centralizer ({x5 * x3} : Set R)) ∣ 30) :
    Nat.card (centralizer S) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hx5p : x5 ^ 5 = 1 := by rw [← hx5]; exact pow_orderOf_eq_one x5
  have hx3p : x3 ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x3
  set y := x5 * x3 with hy
  set D := centralizer S with hD
  have hDC : D ≤ centralizer ({y} : Set R) := by
    intro d hd
    rw [mem_centralizer_singleton_iff]
    have h5 : Commute d x5 := (mem_centralizer_iff.1 hd x5 h5S).symm
    have h3 : Commute d x3 := (mem_centralizer_iff.1 hd x3 h3S).symm
    exact (h5.mul_right h3).eq
  have hcomm : Commute x5 x3 := hc
  have hp5 : x5 ^ 6 = x5 := by rw [pow_succ, hx5p, one_mul]
  have hp3 : x3 ^ 6 = 1 := by rw [show 6 = 3 * 2 from rfl, pow_mul, hx3p, one_pow]
  have hq5 : x5 ^ 10 = 1 := by rw [show 10 = 5 * 2 from rfl, pow_mul, hx5p, one_pow]
  have hq3 : x3 ^ 10 = x3 := by
    rw [show 10 = 3 * 3 + 1 from rfl, pow_succ, pow_mul, hx3p, one_pow, one_mul]
  have hx5y : x5 = y ^ 6 := by rw [hy, hcomm.mul_pow, hp5, hp3, mul_one]
  have hx3y : x3 = y ^ 10 := by rw [hy, hcomm.mul_pow, hq5, hq3, one_mul]
  have h5nd : ¬ 5 ^ 2 ∣ Nat.card (centralizer ({y} : Set R)) :=
    fun h => (by decide : ¬ (5 ^ 2 ∣ 30)) (h.trans hC)
  have h3nd : ¬ 3 ^ 2 ∣ Nat.card (centralizer ({y} : Set R)) :=
    fun h => (by decide : ¬ (3 ^ 2 ∣ 30)) (h.trans hC)
  have hd5 : ∀ d ∈ D, d ^ 5 = 1 → d = 1 := fun d hd hdp =>
    eq_one_of_pow_prime hx5y hx5 hn5 hDC h5nd hd hdp
  have hd3 : ∀ d ∈ D, d ^ 3 = 1 → d = 1 := fun d hd hdp =>
    eq_one_of_pow_prime hx3y hx3 hn3 hDC h3nd hd hdp
  have hnd : ∀ p : ℕ, Fact p.Prime → (∀ d ∈ D, d ^ p = 1 → d = 1) → ¬ p ∣ Nat.card D := by
    intro p hp h hpD
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) p hpD
    have hxo : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hx1 : x = 1 := Subtype.ext (h x x.2 (by simpa using congrArg Subtype.val hxo))
    rw [hx1, orderOf_one] at hx
    exact hp.out.ne_one hx.symm
  have hdvd : Nat.card D ∣ 30 := (card_dvd_of_le hDC).trans hC
  have hc3 : Nat.Coprime (Nat.card D) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (hnd 3 inferInstance hd3)).symm
  have hc5 : Nat.Coprime (Nat.card D) 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 (hnd 5 inferInstance hd5)).symm
  have hc15 : Nat.Coprime (Nat.card D) 15 := by simpa using Nat.Coprime.mul_right hc3 hc5
  have h2 : Nat.card D ∣ 2 :=
    hc15.dvd_of_dvd_mul_right (by simpa using hdvd : Nat.card D ∣ 2 * 15)
  exact Nat.le_of_dvd (by norm_num) h2

end CFSG.EvenSporadicStandard.HSStd.PumpT
