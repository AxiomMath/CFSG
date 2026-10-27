module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G]

theorem sr630e_conj_eq_of_odd {p : ℕ} (hp : p.Prime) (hp35 : p = 3 ∨ p = 5) {x n : G}
    (hx : orderOf x = p) (hn : Odd (orderOf n)) {j : ℤ} (hj : x ^ j = n * x * n⁻¹) :
    n * x * n⁻¹ = x := by
  have : Fact p.Prime := ⟨hp⟩
  have hiter : ∀ m : ℕ, n ^ m * x * (n ^ m)⁻¹ = x ^ (j ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc n ^ (m + 1) * x * (n ^ (m + 1))⁻¹ = n * (n ^ m * x * (n ^ m)⁻¹) * n⁻¹ := by group
        _ = n * x ^ (j ^ m) * n⁻¹ := by rw [ih]
        _ = (n * x * n⁻¹) ^ (j ^ m) := conj_zpow.symm
        _ = (x ^ j) ^ (j ^ m) := by rw [hj]
        _ = x ^ (j ^ (m + 1)) := by rw [← zpow_mul, pow_succ, mul_comm]
  have h1 : x ^ (j ^ orderOf n) = x := by
    rw [← hiter, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
  have hdiv : (p : ℤ) ∣ j ^ orderOf n - 1 := by
    rw [← hx, orderOf_dvd_iff_zpow_eq_one, zpow_sub, h1, zpow_one, mul_inv_cancel]
  have hj0 : ¬ (p : ℤ) ∣ j := by
    intro h
    rw [← hx, orderOf_dvd_iff_zpow_eq_one] at h
    rw [h] at hj
    have h2 : n * x = n * 1 := (mul_inv_eq_one.mp hj.symm).trans (mul_one n).symm
    have hx1 : x = 1 := mul_left_cancel h2
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hu0 : (j : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hj0
  have hum : (j : ZMod p) ^ orderOf n = 1 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv
    push_cast at h
    exact sub_eq_zero.mp h
  have hup : (j : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hu0
  have h2 : Nat.Coprime (orderOf n) 2 := Nat.coprime_two_right.mpr hn
  have hgcd : Nat.gcd (orderOf n) (p - 1) = 1 := by
    rcases hp35 with rfl | rfl
    · exact h2
    · exact Nat.Coprime.pow_right 2 h2
  have hu1 : (j : ZMod p) = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hum, hup⟩
    rwa [hgcd, pow_one] at h
  have hj1 : (p : ℤ) ∣ j - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hu1, sub_self]
  have hx1 : x ^ (j - 1) = 1 := by
    rw [← hx, orderOf_dvd_iff_zpow_eq_one] at hj1
    exact hj1
  rw [← hj]
  calc x ^ j = x ^ (j - 1) * x := by rw [← zpow_add_one, sub_add_cancel]
    _ = x := by rw [hx1, one_mul]

variable [Finite G]

theorem sr630e_normal_complement {p : ℕ} (hp : p.Prime) (hp35 : p = 3 ∨ p = 5) {C : Subgroup G}
    {x : G} (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hsyl : IsSylowOf p (zpowers x) C)
    (hodd : ¬ 2 ∣ Nat.card C) :
    ∃ K : Subgroup G, K ≤ C ∧ Nat.card C = Nat.card K * p ∧ ¬ p ∣ Nat.card K ∧
      ∀ g ∈ C, (g ∈ K ↔ Nat.Coprime p (orderOf g)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hxC : x ∈ C := hsyl.le (mem_zpowers x)
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hcQ := hsyl.card_eq
  rw [Nat.card_zpowers, hxo] at hcQ
  obtain ⟨Q, hQ⟩ := hsyl
  have hQx : (Q : Subgroup C) = zpowers (⟨x, hxC⟩ : C) := by
    apply Subgroup.map_injective C.subtype_injective
    rw [hQ, MonoidHom.map_zpowers]
    rfl
  have hxco : orderOf (⟨x, hxC⟩ : C) = p := by rw [Subgroup.orderOf_mk]; exact hxo
  have hN : normalizer ((Q : Subgroup C) : Set C) ≤ centralizer ((Q : Subgroup C) : Set C) := by
    intro n hn
    rw [hQx] at hn ⊢
    have hodd' : Odd (orderOf n) := by
      have hdvd : orderOf n ∣ Nat.card C := orderOf_dvd_natCard n
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => hodd (h.trans hdvd))
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp
      ((mem_normalizer_iff.mp hn ⟨x, hxC⟩).mp (mem_zpowers _))
    have hcomm := sr630e_conj_eq_of_odd hp hp35 hxco hodd' hj
    have h2 : Commute (⟨x, hxC⟩ : C) n := by
      calc (⟨x, hxC⟩ : C) * n = n * (⟨x, hxC⟩ : C) * n⁻¹ * n := by rw [hcomm]
        _ = n * (⟨x, hxC⟩ : C) := by group
    rw [mem_centralizer_iff]
    intro q hq
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hq
    exact (h2.zpow_left i).eq
  have hK := MonoidHom.ker_transferSylow_isComplement' Q hN
  have hKn : (MonoidHom.transferSylow Q hN).ker.Normal := MonoidHom.normal_ker _
  have hQc : Nat.card (Q : Subgroup C) = p := by rw [hQx, Nat.card_zpowers, hxco]
  have hcard : Nat.card (MonoidHom.transferSylow Q hN).ker * p = Nat.card C := by
    have h := hK.card_mul_card
    rwa [hQc] at h
  have hidx : (MonoidHom.transferSylow Q hN).ker.index = p := by
    have h := (MonoidHom.transferSylow Q hN).ker.card_mul_index
    have hK0 : 0 < Nat.card (MonoidHom.transferSylow Q hN).ker := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hK0 (h.trans hcard.symm)
  have hpK : ¬ p ∣ Nat.card (MonoidHom.transferSylow Q hN).ker := by
    intro h
    have h2 : p ^ 2 ∣ Nat.card C := by
      rw [← hcard, pow_two]
      exact Nat.mul_dvd_mul_right h p
    have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
    have h3 := (hp.pow_dvd_iff_le_factorization hC0).mp h2
    have h4 : p ^ 2 ≤ p ^ (Nat.card C).factorization p := Nat.pow_le_pow_right hp.pos h3
    rw [← hcQ] at h4
    have h5 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h5
    omega
  refine ⟨(MonoidHom.transferSylow Q hN).ker.map C.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hcard.symm
  · rwa [Subgroup.card_map_of_injective C.subtype_injective]
  · intro g hg
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hdvd : orderOf k ∣ Nat.card (MonoidHom.transferSylow Q hN).ker := by
        have h := orderOf_dvd_natCard (⟨k, hk⟩ : (MonoidHom.transferSylow Q hN).ker)
        rwa [Subgroup.orderOf_mk] at h
      have hcop : Nat.Coprime p (Nat.card (MonoidHom.transferSylow Q hN).ker) :=
        (Nat.Prime.coprime_iff_not_dvd hp).mpr hpK
      rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
      exact hcop.coprime_dvd_right hdvd
    · intro hcop
      have hgK : (⟨g, hg⟩ : C) ^ (MonoidHom.transferSylow Q hN).ker.index ∈
          (MonoidHom.transferSylow Q hN).ker := Subgroup.pow_index_mem _ _
      rw [hidx] at hgK
      have hcop' : Nat.Coprime p (orderOf (⟨g, hg⟩ : C)) := by rwa [Subgroup.orderOf_mk]
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop'
      have hmem : (⟨g, hg⟩ : C) ∈ (MonoidHom.transferSylow Q hN).ker := by
        rw [← hm]
        exact pow_mem hgK m
      exact ⟨⟨g, hg⟩, hmem, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
