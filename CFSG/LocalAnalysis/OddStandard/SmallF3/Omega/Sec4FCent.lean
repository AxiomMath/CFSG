module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FCentSq

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.cent_two_elt (h : Sec4FSetup t L S z A B φ) {c : G}
    (hc : c ∈ centralizer (A : Set G)) (hn : ∃ n : ℕ, c ^ (2 ^ n) = 1) : c ∈ A := by
  obtain ⟨n, hn⟩ := hn
  have hcA : ∀ a ∈ A, a * c = c * a := Subgroup.mem_centralizer_iff.mp hc
  have hc_ct : c ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcA t h.t_mem_A).symm
  have hcN : c ∈ normalizer (L : Set G) := h.cent_le_normalizer hc_ct
  have hcB : ∀ b ∈ B, c * b = b * c := fun b hb => (hcA b (h.B_le_A hb)).symm
  have hmem : c ∈ B ⊔ centralizer (L : Set G) := h.mem_B_sup_cent hcN hcB
  have hcomm : ∀ a ∈ B, ∀ b ∈ centralizer (L : Set G), a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb a (h.B_le_L ha)
  obtain ⟨b, hbB, h', hh'C, hceq⟩ := sec4F_mem_sup_comm hcomm hmem
  have hbA : b ∈ A := h.B_le_A hbB
  have hbc : Commute b c := hcA b hbA
  have hbsq : b * b = 1 := h.A_sq hbA
  have hbt : Commute b t := h.A_comm hbA h.t_mem_A
  have hct : Commute c t := Subgroup.mem_centralizer_singleton_iff.mp hc_ct
  have hh'_eq : h' = b⁻¹ * c := by rw [hceq]; group
  have hh't : Commute h' t := by
    rw [hh'_eq]
    exact hbt.inv_left.mul_left hct
  have hcyc : ∀ P : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (P : Subgroup (centralizer (L : Set G))) :=
    h.inputs.h42 G t L h.ctx.toSec4Setting
  have hbsq' : b⁻¹ * b⁻¹ = 1 := by rw [← mul_inv_rev, hbsq, inv_one]
  have hbpow : b⁻¹ ^ (2 ^ (n + 1)) = 1 := by
    rw [show (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n by rw [pow_succ'], pow_mul, pow_two, hbsq',
      one_pow]
  have hcsq : (c ^ (2 ^ n)) ^ 2 = 1 := by rw [hn, one_pow]
  have hcpow : c ^ (2 ^ (n + 1)) = 1 := by rw [pow_succ, pow_mul, hcsq]
  have hpow : h' ^ (2 ^ (n + 1)) = 1 := by
    rw [hh'_eq, Commute.mul_pow hbc.inv_left (2 ^ (n + 1)), hbpow, hcpow, one_mul]
  have hdvd : orderOf h' ∣ 2 ^ (n + 1) := orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨k, _hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hh'A : h' ∈ A := by
    rcases k with _ | k
    · have hk1 : orderOf h' = 1 := by simpa using hk
      rw [orderOf_eq_one_iff.mp hk1]
      exact A.one_mem
    rcases k with _ | k
    · have hk2 : orderOf h' = 2 := by simpa using hk
      have hh'sq : h' * h' = 1 := by
        have h2 := pow_orderOf_eq_one h'
        rwa [hk2, pow_two] at h2
      rcases sec4_eq_of_commute (H := centralizer (L : Set G)) hcyc hh'C h.t_mem_cent hh'sq
        h.ctx.involution hh't with h1 | h1
      · rw [h1]; exact A.one_mem
      · rw [h1]; exact h.t_mem_A
    · exfalso
      have hk' : orderOf h' = 2 ^ (k + 2) := hk
      let c₀ : G := h' ^ (2 ^ k)
      have hc₀C : c₀ ∈ centralizer (L : Set G) :=
        Subgroup.pow_mem (centralizer (L : Set G)) hh'C (2 ^ k)
      have h2k : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [← two_mul, pow_succ']
      have hu_eq : c₀ * c₀ = h' ^ (2 ^ (k + 1)) := by
        show h' ^ (2 ^ k) * h' ^ (2 ^ k) = h' ^ (2 ^ (k + 1))
        rw [← pow_add, h2k]
      have hdvd_u : 2 ^ (k + 1) ∣ orderOf h' := by
        rw [hk']
        exact ⟨2, by rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]⟩
      have hu_ord : orderOf (h' ^ (2 ^ (k + 1))) = 2 := by
        rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) hdvd_u, hk',
          Nat.pow_div (by omega) (by norm_num : (0 : ℕ) < 2)]
        rw [show k + 2 - (k + 1) = 1 by omega, pow_one]
      have hu_sq : (h' ^ (2 ^ (k + 1))) * (h' ^ (2 ^ (k + 1))) = 1 := by
        have h2 := pow_orderOf_eq_one (h' ^ (2 ^ (k + 1)))
        rwa [hu_ord, pow_two] at h2
      have hu_ne_one : h' ^ (2 ^ (k + 1)) ≠ 1 := by
        intro h1
        have h3 : orderOf (h' ^ (2 ^ (k + 1))) = 1 := by rw [h1, orderOf_one]
        rw [hu_ord] at h3
        exact absurd h3 (by decide)
      have huC : h' ^ (2 ^ (k + 1)) ∈ centralizer (L : Set G) :=
        Subgroup.pow_mem (centralizer (L : Set G)) hh'C (2 ^ (k + 1))
      have hut : (h' ^ (2 ^ (k + 1))) * t = t * (h' ^ (2 ^ (k + 1))) :=
        (hh't.pow_left (2 ^ (k + 1))).eq
      rcases sec4_eq_of_commute (H := centralizer (L : Set G)) hcyc huC h.t_mem_cent hu_sq
        h.ctx.involution hut with hu1 | hut'
      · exact absurd hu1 hu_ne_one
      · exact h.no_sqrt_t hc₀C (by rw [hu_eq, hut'])
  rw [hceq]
  exact A.mul_mem (h.B_le_A hbB) hh'A

end CFSG.OddStandard.SmallF3.Omega
