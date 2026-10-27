module

public import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.GroupTheory.SteinbergBKSolvableHallConjugacy

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint

theorem exists_conj_mem_suzukiT_of_mem_suzukiB_of_odd
    {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : suzukiGroup a K}
    (hgB : g ∈ suzukiB a K) (hodd : Odd (orderOf g)) :
    ∃ v ∈ suzukiB a K, v * g * v⁻¹ ∈ suzukiT a K := by
  classical
  let π : Set Nat.Primes := {p | p.val ≠ 2}
  have hBsolv : Group.IsSolvable ↥(suzukiB a K) := (suzuki_borel_solvable hK).1
  let gB : ↥(suzukiB a K) := ⟨g, hgB⟩
  have hgπ : IsPiSubgroup π (Subgroup.zpowers gB) := by
    intro p hp
    change p.val ≠ 2
    intro hp2
    have hdvd : p.val ∣ Nat.card (Subgroup.zpowers gB) := hp
    rw [Nat.card_zpowers] at hdvd
    have hdvd' : p.val ∣ orderOf g := by
      rwa [Subgroup.orderOf_mk] at hdvd
    have h2dvd : 2 ∣ orderOf g := by simpa [hp2] using hdvd'
    exact (Odd.not_two_dvd_nat hodd) h2dvd
  have hTHall : IsHallSubgroup π ((suzukiT a K).subgroupOf (suzukiB a K)) := by
    refine CFSG.isHallSubgroup_of π ((suzukiT a K).subgroupOf (suzukiB a K)) ?_ ?_
    · intro p hp
      change p.val ≠ 2
      have hcardT : Nat.card ↥((suzukiT a K).subgroupOf (suzukiB a K)) =
          Nat.card (suzukiT a K) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suzukiT_le_suzukiB a K))
      have hTodd : Odd (Nat.card (suzukiT a K)) := by
        have hcard : Nat.card (suzukiT a K) = Nat.card Kˣ := by
          rw [(suzuki_borel_structure hK).2.2.1, Nat.card_units, hK]
        rw [hcard]
        exact odd_card_units hK
      exact (Odd.of_dvd_nat hTodd (by rwa [hcardT] at hp)).ne_two_of_dvd_nat
        (dvd_refl p.val)
    · intro p hp hpdiv
      change p.val ≠ 2 at hp
      have hcardT : Nat.card ↥((suzukiT a K).subgroupOf (suzukiB a K)) =
          Nat.card (suzukiT a K) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suzukiT_le_suzukiB a K))
      have hindex : ((suzukiT a K).subgroupOf (suzukiB a K)).index =
          (2 ^ (2 * a + 1)) ^ 2 := by
        have h1 := Subgroup.card_mul_index ((suzukiT a K).subgroupOf (suzukiB a K))
        have hcardB : Nat.card ↥(suzukiB a K) =
            (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) :=
          (suzuki_borel_structure hK).2.2.2.2.2.2.2
        have hcardT' : Nat.card (suzukiT a K) = 2 ^ (2 * a + 1) - 1 :=
          (suzuki_borel_structure hK).2.2.1
        rw [hcardT, hcardT', hcardB] at h1
        have hq1 : 0 < 2 ^ (2 * a + 1) - 1 := by
          have : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
          omega
        have h1' : (2 ^ (2 * a + 1) - 1) *
            ((suzukiT a K).subgroupOf (suzukiB a K)).index =
            (2 ^ (2 * a + 1) - 1) * (2 ^ (2 * a + 1)) ^ 2 := by
          rw [h1]
          ring
        exact Nat.eq_of_mul_eq_mul_left hq1 h1'
      have hpow : (2 ^ (2 * a + 1)) ^ 2 = 2 ^ (2 * (2 * a + 1)) := by
        ring_nf
      have hpdvd : p.val ∣ (2 : ℕ) ^ (2 * (2 * a + 1)) := by
        have h := hpdiv
        rw [hindex, hpow] at h
        exact h
      have hp2 : p.val ∣ 2 := Nat.Prime.dvd_of_dvd_pow p.2 hpdvd
      have hpeq : p.val = 2 := (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).mp hp2
      exact hp hpeq
  obtain ⟨H, hHHall, hgH⟩ := CFSG.SolvableHall.solvable_hall_containment hBsolv π
    (Subgroup.zpowers gB) hgπ
  obtain ⟨v, hv⟩ := CFSG.GroupTheory.SteinbergBK.solvable_hall_conjugacy hBsolv
    hTHall hHHall
  have hgHmem : gB ∈ H := hgH (Subgroup.mem_zpowers gB)
  have hgConj : gB ∈ CFSG.conjugate ((suzukiT a K).subgroupOf (suzukiB a K)) v := by
    simpa [hv] using hgHmem
  obtain ⟨t, htT, ht_eq⟩ := Subgroup.mem_map.mp hgConj
  have ht_eq' : (v : ↥(suzukiB a K))⁻¹ * t * (v : ↥(suzukiB a K)) = gB := by
    simpa [CFSG.conjugate, MulAut.conj_apply] using ht_eq
  let t0 : suzukiGroup a K := (t : ↥(suzukiB a K))
  let vv : suzukiGroup a K := (v : ↥(suzukiB a K))
  have ht0T : t0 ∈ suzukiT a K := Subgroup.mem_subgroupOf.mp htT
  have ht0_eq : t0 = vv * g * vv⁻¹ := by
    have h : vv⁻¹ * t0 * vv = g := by
      simpa [t0, vv, gB] using congrArg Subtype.val ht_eq'
    calc t0 = vv * (vv⁻¹ * t0 * vv) * vv⁻¹ := by group
      _ = vv * g * vv⁻¹ := by rw [h]
  refine ⟨vv, Subgroup.mem_subgroupOf.mp v.2, ?_⟩
  rw [← ht0_eq]
  exact ht0T

end CFSG.LieType.Ree

end
