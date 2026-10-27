module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallSDFix
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallSD
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallWeak

public section

namespace CFSG.ComponentClassification.Foote5.Asc25

open CFSG Subgroup CFSG.ComponentClassification.Foote5.HallGen

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

omit [Finite G] in
theorem eq_one_of_odd_of_pow {a : G} {r k : ℕ} (hr : Odd r) (ha : a ^ r = 1)
    (hk : a ^ (2 ^ k) = 1) : a = 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one ha
  have h2 := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime r (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hr)
  have h3 : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp h3

theorem commute_c_of_odd {m : ℕ} (hm : orderOf c = 2 ^ m) {y : G} (hodd : Odd (orderOf y))
    (hyN : y ∈ normalizer (zpowers c : Set G)) : y * c = c * y := by
  set C := zpowers c with hC
  set φ := C.normalizerMonoidHom ⟨y, hyN⟩ with hφ
  have h1 : orderOf φ ∣ orderOf y := by
    have := orderOf_map_dvd C.normalizerMonoidHom ⟨y, hyN⟩
    rwa [Subgroup.orderOf_mk] at this
  have hcardC : Nat.card C = 2 ^ m := by rw [hC, Nat.card_zpowers, hm]
  have h2 : orderOf φ ∣ 2 ^ m := by
    have h := orderOf_dvd_natCard φ
    rw [IsCyclic.card_mulAut, hcardC] at h
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [pow_zero, Nat.totient_one] at h
      exact h.trans (one_dvd _)
    · rw [Nat.totient_prime_pow Nat.prime_two hm0, show (2 : ℕ) - 1 = 1 from rfl, mul_one] at h
      exact h.trans (Nat.pow_dvd_pow 2 (Nat.sub_le m 1))
  have hcop : Nat.Coprime (orderOf y) (2 ^ m) :=
    Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)
  have h3 : orderOf φ = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at h3
  have h4 := congrArg Subtype.val (MulEquiv.ext_iff.mp h3 ⟨c, mem_zpowers c⟩)
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h4
  change y * c * y⁻¹ = c at h4
  calc y * c = y * c * y⁻¹ * y := by group
    _ = c * y := by rw [h4]

variable (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹)) (hk : 4 ∣ orderOf c)
include hD hk

theorem commute_of_odd_of_mem_normalizer {m : ℕ} (hm : orderOf c = 2 ^ m) (hcD : c ∈ D) {y : G}
    (hodd : Odd (orderOf y)) (hyN : y ∈ normalizer (D : Set G)) {d : G} (hd : d ∈ D) :
    y * d = d * y := by
  have hyC : y ∈ normalizer (zpowers c : Set G) :=
    le_normalizer_zpowers_c hD hk hcD hyN
  have hyc := commute_c_of_odd hm hodd hyC
  have hycz : ∀ i : ℤ, y * c ^ i = c ^ i * y := fun i => (Commute.zpow_right hyc i).eq
  by_cases hdC : d ∈ zpowers c
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hdC
    exact hycz i
  have hd2 : d * d = 1 := by
    rcases hD d hd with h | ⟨h, -⟩
    · exact absurd h hdC
    · exact h
  have hydD : y * d * y⁻¹ ∈ D := (mem_normalizer_iff.mp hyN d).mp hd
  have hydC := conj_not_mem_zpowers hD hk hyN hcD hdC
  obtain ⟨l, hl⟩ := mem_zpowers_iff.mp (mul_mem_zpowers_of_refl hD hk hydD hd hydC hdC)
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hyd : y * d * y⁻¹ = c ^ l * d := by
    calc y * d * y⁻¹ = y * d * y⁻¹ * d * d⁻¹ := by group
      _ = c ^ l * d := by rw [hl, hdi]
  have hpow : ∀ r : ℕ, y ^ r * d * (y ^ r)⁻¹ = c ^ (l * r) * d := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      calc y ^ (r + 1) * d * (y ^ (r + 1))⁻¹ = y * (y ^ r * d * (y ^ r)⁻¹) * y⁻¹ := by
            rw [pow_succ']
            group
        _ = y * (c ^ (l * r) * d) * y⁻¹ := by rw [ih]
        _ = c ^ (l * r) * (y * d * y⁻¹) := by rw [← mul_assoc y, hycz]; group
        _ = c ^ (l * (r + 1 : ℕ)) * d := by
            rw [hyd, ← mul_assoc, ← zpow_add]
            congr 2
            push_cast
            ring
  have hr := hpow (orderOf y)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hr
  have hcl : (c ^ l) ^ orderOf y = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    have : c ^ (l * (orderOf y : ℤ)) * d = 1 * d := by rw [← hr, one_mul]
    exact mul_right_cancel this
  have hcl2 : (c ^ l) ^ (2 ^ m) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hm, pow_orderOf_eq_one,
      one_zpow]
  have hcl1 := eq_one_of_odd_of_pow hodd hcl hcl2
  calc y * d = y * d * y⁻¹ * y := by group
    _ = d * y := by rw [hyd, hcl1, one_mul]

theorem commute_of_odd_sup {m : ℕ} (hm : orderOf c = 2 ^ m) (hcD : c ∈ D)
    (hcard : Nat.card D = 2 * orderOf c) {S₀ : Subgroup G} (hDS : D ≤ S₀)
    (hcardS : Nat.card S₀ ≤ 2 * Nat.card D) (hinv : ∀ x ∈ S₀, x * x = 1 → x ∈ D) {y : G}
    (hodd : Odd (orderOf y)) (hyN : y ∈ normalizer (S₀ : Set G)) {s : G} (hs : s ∈ S₀) :
    y * s = s * y := by
  have hconjD : ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
    intro d hd
    obtain ⟨a, ha, b, hb, ha2, hb2, rfl⟩ := exists_mul hD hcard hd
    have hsq : ∀ e ∈ D, e * e = 1 → y * e * y⁻¹ ∈ D := fun e he he2 =>
      hinv _ ((mem_normalizer_iff.mp hyN e).mp (hDS he)) (by
        rw [show y * e * y⁻¹ * (y * e * y⁻¹) = y * (e * e) * y⁻¹ by group, he2]
        group)
    rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group]
    exact mul_mem (hsq a ha ha2) (hsq b hb hb2)
  have hyD : y ∈ normalizer (D : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj y).injective).ge
    rintro _ ⟨d, hd, rfl⟩
    exact hconjD d hd
  have hcomm : ∀ d ∈ D, y * d = d * y := fun d hd =>
    commute_of_odd_of_mem_normalizer hD hk hm hcD hodd hyD hd
  by_cases hsD : s ∈ D
  · exact hcomm s hsD
  have hs'S : y * s * y⁻¹ ∈ S₀ := (mem_normalizer_iff.mp hyN s).mp hs
  have hs'D : y * s * y⁻¹ ∉ D := fun h => hsD (by
    have h1 := (mem_normalizer_iff.mp (inv_mem hyD) _).mp h
    rwa [show y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ = s by group] at h1)
  have hd₀ := inv_mul_mem_of_card_le hDS hcardS hs hs'S hsD hs'D
  set d₀ := s⁻¹ * (y * s * y⁻¹) with hd₀def
  have hys : y * s * y⁻¹ = s * d₀ := by rw [hd₀def]; group
  have hpow : ∀ r : ℕ, y ^ r * s * (y ^ r)⁻¹ = s * d₀ ^ r := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      calc y ^ (r + 1) * s * (y ^ (r + 1))⁻¹ = y * (y ^ r * s * (y ^ r)⁻¹) * y⁻¹ := by
            rw [pow_succ']
            group
        _ = y * (s * d₀ ^ r) * y⁻¹ := by rw [ih]
        _ = (y * s * y⁻¹) * (y * d₀ ^ r * y⁻¹) := by group
        _ = s * d₀ ^ (r + 1) := by
            rw [hys, hcomm _ (pow_mem hd₀ r), mul_inv_cancel_right, pow_succ', mul_assoc]
  have hr := hpow (orderOf y)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hr
  have hd₀r : d₀ ^ orderOf y = 1 := by
    have : s * d₀ ^ orderOf y = s * 1 := by rw [← hr, mul_one]
    exact mul_left_cancel this
  have hd₀k : d₀ ^ (2 ^ (m + 1)) = 1 := by
    have h1 := pow_card_eq_one' (G := D) (x := ⟨d₀, hd₀⟩)
    rw [hcard, hm, ← pow_succ'] at h1
    exact congrArg Subtype.val h1
  have h1 := eq_one_of_odd_of_pow hodd hd₀r hd₀k
  rw [h1, mul_one] at hys
  calc y * s = y * s * y⁻¹ * y := by group
    _ = s * y := by rw [hys]

theorem pow_mem_centralizer {m : ℕ} (hm : orderOf c = 2 ^ m) (hcD : c ∈ D)
    (hcard : Nat.card D = 2 * orderOf c) {S₀ : Subgroup G} (hDS : D ≤ S₀)
    (hcardS : Nat.card S₀ ≤ 2 * Nat.card D) (hinv : ∀ x ∈ S₀, x * x = 1 → x ∈ D) :
    ∀ n ∈ normalizer (S₀ : Set G), ∃ k : ℕ, n ^ (2 ^ k) ∈ centralizer (S₀ : Set G) := by
  intro n hn
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  refine ⟨a, ?_⟩
  have hord : orderOf (n ^ (2 ^ a)) = b := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hab]; exact Dvd.intro b rfl), hab,
      Nat.mul_div_cancel_left _ (by positivity)]
  rw [mem_centralizer_iff]
  intro s hs
  exact (commute_of_odd_sup hD hk hm hcD hcard hDS hcardS hinv (hord ▸ hb) (pow_mem hn _)
    hs).symm

end CFSG.ComponentClassification.Foote5.Asc25
