module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0KernelLemma

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}
  {N : Subgroup J}

namespace A0Config

theorem conj_eq_of_mem_a0Kernel (hc : A0Config Q B z u N) {k : J} (hk : k ∈ a0Kernel Q B N) :
    z * k * z⁻¹ = k ∨ z * k * z⁻¹ = centralElt J * k :=
  hc.setting.conj_eq_of_comm_mem_center (hc.fourGen.comm_mem_center' hk.1)

theorem conj_self_eq_of_mem_a0Kernel (hc : A0Config Q B z u N) {k : J}
    (hk : k ∈ a0Kernel Q B N) : u * k * u⁻¹ = k ∨ u * k * u⁻¹ = centralElt J * k :=
  hc.setting.conj_eq_of_comm_mem_center ((commute_mk_iff u k).mp ((commute_mk_iff k u).mpr
    ((hc.setting.mem_normalizer_zpowers_iff hc.sq).mp (hc.mem_quasiNormalizer hk.1))).symm)

theorem mul_eq_central_mul_of_mem_a0Kernel (hc : A0Config Q B z u N) {k : J}
    (hk : k ∈ a0Kernel Q B N) (hkk : k * k = centralElt J) (hku : k ≠ u)
    (hkeu : k ≠ centralElt J * u) : u * k = centralElt J * (k * u) := by
  have h := hc.setting
  rcases hc.conj_self_eq_of_mem_a0Kernel hk with h1 | h1
  · exfalso
    have huk : u * k = k * u := by
      calc u * k = u * k * u⁻¹ * u := by group
        _ = k * u := by rw [h1]
    have hmem : u * k⁻¹ ∈ a0Kernel Q B N :=
      (a0Kernel Q B N).mul_mem hc.self_mem_a0Kernel ((a0Kernel Q B N).inv_mem hk)
    have hsq : u * k⁻¹ * (u * k⁻¹) = 1 := by
      have hk' : k⁻¹ * u = u * k⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← huk, mul_assoc, mul_inv_cancel, mul_one]
      calc u * k⁻¹ * (u * k⁻¹) = u * u * (k * k)⁻¹ := by
            rw [mul_assoc u, ← mul_assoc k⁻¹, hk']; group
        _ = 1 := by rw [hc.sq, hkk, mul_inv_cancel]
    by_cases h2 : u * k⁻¹ = 1
    · exact hku (by rw [mul_inv_eq_one] at h2; exact h2.symm)
    · have h3 := hc.eq_centralElt_of_mem_a0Kernel hmem
        (orderOf_eq_prime (by rw [pow_two]; exact hsq) h2)
      apply hkeu
      rw [mul_inv_eq_iff_eq_mul] at h3
      rw [h3, ← mul_assoc, h.centralElt_mul_self, one_mul]
  · calc u * k = u * k * u⁻¹ * u := by group
      _ = centralElt J * (k * u) := by rw [h1, mul_assoc]

theorem conj_mul_eq_central_mul (hc : A0Config Q B z u N) {t : J}
    (htQ : t ∈ (Q : Subgroup J)) (ht : t * t = 1) (htV : t ∉ fourGroup z) :
    z * (z * t) * z⁻¹ = centralElt J * (z * t) := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hc.fourGen.mul_self
  calc z * (z * t) * z⁻¹ = t * z := by rw [hzinv, ← mul_assoc, hc.fourGen.mul_self, one_mul]
    _ = t * z * t⁻¹ * t := by group
    _ = centralElt J * (z * t) := by rw [hc.conj_eq_of_not_mem htQ ht htV, mul_assoc]

theorem conj_self_eq_conj_inv (hc : A0Config Q B z u N) (k : J) :
    u * k * u⁻¹ = u⁻¹ * k * u := by
  rw [hc.setting.inv_eq_central_mul hc.sq, hc.setting.mul_central_left]
  simp only [mul_assoc]

theorem typeOne_iff (hc : A0Config Q B z u N) :
    (∀ k ∈ a0Kernel Q B N, z * k * z⁻¹ = u * k * u⁻¹) ↔
      ∀ k ∈ a0Kernel Q B N, u * z * k = k * (u * z) := by
  refine ⟨fun h1 k hk => ?_, fun h1 k hk => ?_⟩
  · calc u * z * k = u * (z * k * z⁻¹) * z := by group
      _ = k * (u * z) := by rw [h1 k hk, hc.conj_self_eq_conj_inv k]; group
  · calc z * k * z⁻¹ = u⁻¹ * (u * z * k) * z⁻¹ := by group
      _ = u * k * u⁻¹ := by rw [h1 k hk, hc.conj_self_eq_conj_inv k]; group

theorem typeOne_of_card_eq_eight (hc : A0Config Q B z u N)
    (h8 : Nat.card (a0Kernel Q B N) = 8) :
    ∀ k ∈ a0Kernel Q B N, z * k * z⁻¹ = u * k * u⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hc.setting
  rw [hc.typeOne_iff]
  obtain ⟨t, htQ, ht, htV⟩ := hc.fourGen.exists_involution_not_mem_fourGroup h
  set C := a0Kernel Q B N ⊓ Subgroup.centralizer {u * z} with hC
  have huC : u ∈ C := ⟨hc.self_mem_a0Kernel, Subgroup.mem_centralizer_singleton_iff.mpr (by
    rw [← mul_assoc, mul_assoc u z u, ← hc.comm, ← mul_assoc])⟩
  have hztC : z * t ∈ C := by
    refine ⟨hc.mul_mem_a0Kernel htQ ht htV, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have htc : t * (u * z) = u * z * t := by
      calc t * (u * z) = t * (u * z) * t⁻¹ * t := by group
        _ = u * z * t := by rw [hc.conj_mul_eq_of_not_mem htQ ht htV]
    have hzc : z * (u * z) = u * z * z := by rw [← mul_assoc, ← hc.comm]
    rw [mul_assoc, htc, ← mul_assoc, hzc, mul_assoc]
  have hu4 : orderOf u = 4 := by
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · rw [pow_one, pow_two, hc.sq]
      exact h.centralElt_ne_one
    · have h4 : u ^ 4 = u * u * (u * u) := by rw [pow_succ, pow_succ, pow_two]; group
      rw [show 2 ^ (1 + 1) = 4 by norm_num, h4, hc.sq, h.centralElt_mul_self]
  have hlt : Subgroup.zpowers u < C := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr huC) fun heq => ?_
    rw [← heq] at hztC
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hztC
    have h1 : z * t * u = u * (z * t) := by
      rw [← hm]
      exact ((Commute.refl u).zpow_left m).eq
    have h2 := hc.conj_self_eq_of_mul htQ ht htV
    rw [h1, mul_inv_cancel_right] at h2
    exact h.centralElt_ne_one (mul_eq_right.mp h2.symm)
  have hcardC := Subgroup.card_lt_of_lt hlt
  rw [Nat.card_zpowers, hu4] at hcardC
  obtain ⟨m, hm, hCm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card C ∣ 2 ^ 3 by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h8]
      exact Subgroup.card_dvd_of_le inf_le_left)
  have hm3 : m = 3 := by
    rw [hCm] at hcardC
    interval_cases m <;> simp_all
  have hCK : C = a0Kernel Q B N :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hCm, hm3]; norm_num)
  intro k hk
  rw [← hCK] at hk
  exact (Subgroup.mem_centralizer_singleton_iff.mp hk.2).symm

theorem typeOne_or_typeTwo (hc : A0Config Q B z u N) :
    (∀ k ∈ a0Kernel Q B N, z * k * z⁻¹ = u * k * u⁻¹) ∨
      (16 ≤ Nat.card (a0Kernel Q B N) ∧
        ∃ k ∈ a0Kernel Q B N, z * k * z⁻¹ ≠ u * k * u⁻¹) := by
  by_cases h1 : ∀ k ∈ a0Kernel Q B N, z * k * z⁻¹ = u * k * u⁻¹
  · exact Or.inl h1
  · right
    push Not at h1
    refine ⟨?_, h1⟩
    obtain ⟨n, hn, hcard, -⟩ := hc.a0Kernel_quaternion
    have hn3 : n ≠ 3 := fun h3 => by
      obtain ⟨k, hk, hne⟩ := h1
      exact hne (hc.typeOne_of_card_eq_eight (by rw [hcard, h3]; norm_num) k hk)
    rw [hcard]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

end A0Config

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
