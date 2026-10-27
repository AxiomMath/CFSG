module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarCentralizer

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

namespace Setup

variable (S : Setup L z t F L1 N)

include S

theorem mem_L1_of_mem_centralizer {P : Subgroup G} (hP : IsPGroup 2 P) (hL1P : L1 ≤ P) {p : G}
    (hp : p ∈ P) (hpC : p ∈ centralizer (L1 : Set G)) : p ∈ L1 := by
  have hLN : ∀ l ∈ L1, ∀ y ∈ N, l * y * l⁻¹ ∈ N := fun l hl y hy =>
    S.N_norm l (mem_centralizer_iff.2 fun w hw => S.L1_comm w hw l hl) y hy
  have hc : p ∈ N ⊔ L1 := by rw [S.N_sup]; exact hpC
  obtain ⟨n, hn, l, hl, rfl⟩ := exists_mul_of_normalizes hLN hc
  have hnP : n ∈ P := by
    have : n = n * l * l⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hp (Subgroup.inv_mem _ (hL1P hl))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨n, hnP⟩
  have hk' : orderOf n = 2 ^ k := by simpa using hk
  have hn1 : n = 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact orderOf_eq_one_iff.1 (by simpa using hk')
    · exfalso
      apply S.N_odd
      exact dvd_trans (hk' ▸ dvd_pow_self 2 hkpos.ne') (Subgroup.orderOf_dvd_natCard N hn)
  rw [hn1, one_mul]
  exact hl

theorem mem_L1_of_odd_image {P : Subgroup G} (hP : IsPGroup 2 P) (hL1P : L1 ≤ P) {p : G}
    (hp : p ∈ P) (hpX : p ∈ normalizer (L1 : Set G))
    (hodd : Odd (orderOf (QuotientGroup.mk ⟨p, hpX⟩ : Xbar L1))) : p ∈ L1 := by
  apply S.mem_L1_of_mem_centralizer hP hL1P hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨p, hp⟩
  have hk' : orderOf p = 2 ^ k := by simpa using hk
  have hdvd : orderOf (QuotientGroup.mk ⟨p, hpX⟩ : Xbar L1) ∣ 2 ^ k := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' ((centralizer (L1 : Set G)).subgroupOf
      (normalizer (L1 : Set G)))) (⟨p, hpX⟩ : ↥(normalizer (L1 : Set G)))
    have h2 : orderOf (⟨p, hpX⟩ : ↥(normalizer (L1 : Set G))) = orderOf p := by simp
    rw [h2, hk'] at h1
    exact h1
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi0 : i = 0 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact h
    · exfalso
      rw [hi] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, h.ne'⟩)
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  have h1 : (⟨p, hpX⟩ : ↥(normalizer (L1 : Set G))) ∈
      (centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G)) :=
    (QuotientGroup.eq_one_iff _).1 hi
  exact Subgroup.mem_subgroupOf.1 h1

theorem exists_conj_of_odd_image {P : Subgroup G} (hP : IsPGroup 2 P) (hL1P : L1 ≤ P)
    (hzP : z ∈ P) {y : G} (hyP : y ∈ P) (hy2 : y * y = 1) (hyz : y * z ∈ normalizer (L1 : Set G))
    (hodd : Odd (orderOf (QuotientGroup.mk ⟨y * z, hyz⟩ : Xbar L1))) :
    ∃ s ∈ P, y = s⁻¹ * z * s := by
  have hz2 : z * z = 1 := S.one.z_mul_self
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hl : y * z ∈ L1 := S.mem_L1_of_odd_image hP hL1P (P.mul_mem hyP hzP) hyz hodd
  have hy : y = (y * z) * z := by rw [mul_assoc, hz2, mul_one]
  generalize y * z = l at hl hy
  have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right (S.L1_sq l hl)
  have h1 : l * z * (l * z) = 1 := by rw [← hy]; exact hy2
  have hzl : z * l * z = l := by
    have : z * l * z = l⁻¹ := by
      calc z * l * z = l⁻¹ * (l * z * (l * z)) := by group
        _ = l⁻¹ := by rw [h1, mul_one]
    rw [this, hli]
  have hcomm : z * l = l * z := by
    calc z * l = z * l * z * z := by rw [mul_assoc (z * l) z z, hz2, mul_one]
      _ = l * z := by rw [hzl]
  obtain ⟨k, hk, hkl⟩ := S.phi_onto l (S.L1_cz l hl hcomm)
  have hkz : k * z * k⁻¹ = z * l := by
    have h2 : z * (k * z * k⁻¹) = l := hkl
    calc k * z * k⁻¹ = z * (z * (k * z * k⁻¹)) := by rw [← mul_assoc, hz2, one_mul]
      _ = z * l := by rw [h2]
  have hkP : k ∈ P := (sup_le hL1P (Subgroup.zpowers_le.2 hzP)) (S.K_eq ▸ hk)
  refine ⟨k⁻¹, P.inv_mem hkP, ?_⟩
  rw [inv_inv, hkz, hcomm]
  exact hy

section Finite

variable [Finite G]

theorem exists_conj_of_image_eq_one {P : Subgroup G} (hP : IsPGroup 2 P) (hL1P : L1 ≤ P)
    (hzP : z ∈ P) {y : G} (hyP : y ∈ P) (hy2 : y * y = 1) (hyz : y * z ∈ normalizer (L1 : Set G))
    (h1 : (QuotientGroup.mk (QuotientGroup.mk ⟨y * z, hyz⟩ : Xbar L1) :
      Xbar L1 ⧸ fusionOddCore (Xbar L1)) = 1) :
    ∃ s ∈ P, y = s⁻¹ * z * s := by
  have hO : (QuotientGroup.mk ⟨y * z, hyz⟩ : Xbar L1) ∈ fusionOddCore (Xbar L1) :=
    (QuotientGroup.eq_one_iff _).1 h1
  exact S.exists_conj_of_odd_image hP hL1P hzP hyP hy2 hyz
    (Odd.of_dvd_nat (natCard_fusionOddCore_odd (Xbar L1)) (Subgroup.orderOf_dvd_natCard _ hO))

end Finite

end Setup

end CFSG.EvenSporadicStandard.M23Std
