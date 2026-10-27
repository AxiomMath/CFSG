module

public import CFSG.LocalAnalysis.ComponentInitial.CyclicAbelianCentralPair
public import CFSG.LocalAnalysis.ComponentInitial.SmallGroupFacts

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {P : Type*} [Group P]

theorem cyclic_abelian_prime_and_center {p : ℕ} (hp : p.Prime) [Finite P]
    (hP : IsPGroup p P) (hnab : ∃ x y : P, x * y ≠ y * x)
    (hcyc : ∀ B : Subgroup P, IsMulCommutative B → IsCyclic B) :
    p = 2 ∧ Nat.card (center P) = 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hcomp, horder⟩ := cyclic_abelian_center_comparison hp hP hnab hcyc
  obtain ⟨a, b, hmkc, -, hpow, hZgen, -, hab⟩ :=
    cyclic_abelian_central_quotient_pair hp hP hnab hcyc
  set c := b⁻¹ with hc
  set z := c⁻¹ * a⁻¹ * c * a with hzdef
  have hz : z ∈ center P := by
    rw [← QuotientGroup.eq_one_iff]
    have h := (mem_center_iff.1 hmkc (QuotientGroup.mk c : P ⧸ center P))
    simp only [hzdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_assoc, h]
    group
  have hca : c * a = a * c * z := by
    rw [hzdef]
    group
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hca
    apply hab
    have h2 : b⁻¹ * a = a * b⁻¹ := hca
    calc a * b = b * (b⁻¹ * a) * b := by group
      _ = b * (a * b⁻¹) * b := by rw [h2]
      _ = b * a := by group
  have hzc : ∀ g : P, z * g = g * z := fun g => (mem_center_iff.1 hz g).symm
  have hcp : c ^ p = (a ^ p)⁻¹ := by rw [hc, inv_pow, ← hpow]
  have hapZ : a ^ p ∈ center P := hZgen ▸ mem_zpowers (a ^ p)
  have hcpZ : c ^ p ∈ center P := hcp ▸ inv_mem hapZ
  have hzp : z ^ p = 1 := by
    have hconj : a⁻¹ * c * a = c * z := by
      calc a⁻¹ * c * a = a⁻¹ * (c * a) := by group
        _ = a⁻¹ * (a * c * z) := by rw [hca]
        _ = c * z := by group
    have h1 : (a⁻¹ * c * a) ^ p = c ^ p := by
      rw [show a⁻¹ * c * a = a⁻¹ * c * a⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv,
        mul_assoc, ← mem_center_iff.1 hcpZ a, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hconj, (Commute.mul_pow (hzc c).symm p)] at h1
    calc z ^ p = (c ^ p)⁻¹ * (c ^ p * z ^ p) := by group
      _ = 1 := by rw [h1, inv_mul_cancel]
  have hacp : (a * c) ^ p = z ^ p.choose 2 := by
    rw [central_commutation_power hz hca p, hcp, mul_inv_cancel, one_mul]
  have hnotin : a * c ∉ zpowers a := by
    intro h
    have hc' : c ∈ zpowers a := by
      have : c = a⁻¹ * (a * c) := by group
      rw [this]
      exact mul_mem (inv_mem (mem_zpowers a)) h
    have hb' : b ∈ zpowers a := by
      rw [show b = c⁻¹ by rw [hc, inv_inv]]
      exact inv_mem hc'
    obtain ⟨n, hn⟩ := hb'
    apply hab
    rw [← hn]
    exact (Commute.self_zpow a n).eq
  have hZa : center P ≤ zpowers a := by
    rw [← hZgen]
    exact (zpowers_le).2 (pow_mem (mem_zpowers a) p)
  have hacZ : a * c ∉ center P := fun h => hnotin (hZa h)
  have hac1 : a * c ≠ 1 := by
    intro h
    apply hnotin
    rw [h]
    exact one_mem _
  have hp2 : p = 2 := by
    by_contra hp2
    have hodd : Odd p := hp.odd_of_ne_two hp2
    obtain ⟨k, hk⟩ := hodd
    have hch : p.choose 2 = p * k := by
      rw [Nat.choose_two_right, hk]
      rw [show (2 * k + 1) * (2 * k + 1 - 1) = (2 * k + 1) * k * 2 by
        rw [Nat.add_sub_cancel]; ring]
      rw [Nat.mul_div_cancel _ two_pos]
    have h1 : (a * c) ^ p = 1 := by
      rw [hacp, hch, pow_mul, hzp, one_pow]
    have hord : orderOf (a * c) = p := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hac1
      · exact h
    exact hacZ (horder _ hord)
  refine ⟨hp2, ?_⟩
  subst hp2
  have hac2 : (a * c) ^ 2 = z := by rw [hacp]; norm_num
  have hac4 : (a * c) ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, hac2, hzp]
  have hord4 : orderOf (a * c) = 4 := by
    have hdvd : orderOf (a * c) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hac4
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    interval_cases j
    · rw [pow_zero, orderOf_eq_one_iff] at hj'
      exact absurd hj' hac1
    · exfalso
      rw [pow_one] at hj'
      have : (a * c) ^ 2 = 1 := by rw [← hj', pow_orderOf_eq_one]
      rw [hac2] at this
      exact hz1 this
    · rw [hj']
      rfl
  have hlt := (hcomp (a * c) hacZ).2
  rw [hord4] at hlt
  have : Nontrivial (center P) := by
    have : Nontrivial P := by
      obtain ⟨x, y, hxy⟩ := hnab
      exact ⟨⟨x * y, y * x, hxy⟩⟩
    exact hP.center_nontrivial
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hP.to_subgroup (center P))
  have h1 : 1 < Nat.card (center P) := Finite.one_lt_card
  rw [hk] at hlt h1 ⊢
  have hk1 : k ≠ 0 := by
    rintro rfl
    simp at h1
  have hk2 : k < 2 := by
    by_contra h
    push Not at h
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right two_pos h
    omega
  have hk' : k = 1 := by omega
  rw [hk', pow_one]

end CFSG.LocalAnalysis.ComponentInitial
