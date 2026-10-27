module

public import CFSG.GH74.GLS.Stage1.Thm4.Core98

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup

theorem exists_odd_normal_complement {C : Type} [Group C] [Finite C] {D : Subgroup C} (hDn : D.Normal)
    {z : C} (hz : orderOf z = 2) (hzc : ∀ g : C, g * z = z * g) (hzD : z ∈ D)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 (zpowers z) D) :
    ∃ M : Subgroup C, M ≤ D ∧ M.Normal ∧ Odd (Nat.card M) ∧ D ≤ M ⊔ zpowers z := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  have hzle : zpowers z ≤ D := (Subgroup.zpowers_le).2 hzD
  have hQcomm : ∀ q ∈ (Q : Subgroup ↥D), ∀ x : ↥D, q * x = x * q := by
    intro q hq x
    rw [hQ] at hq
    have hq' : (q : C) ∈ zpowers z := hq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hq'
    apply Subtype.ext
    show (q : C) * (x : C) = (x : C) * (q : C)
    rw [← hk]
    have hcx : Commute (x : C) z := hzc x
    exact (hcx.zpow_right k).eq.symm
  have hP : normalizer (Q : Set ↥D) ≤ centralizer (Q : Set ↥D) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hQcomm q hq x
  have hc := MonoidHom.ker_transferSylow_isComplement' Q hP
  set ker := (MonoidHom.transferSylow Q hP).ker with hker
  have hQcard : Nat.card (Q : Subgroup ↥D) = 2 := by
    rw [hQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv, Nat.card_zpowers, hz]
  have hkerIdx : ker.index = 2 := by rw [hc.symm.index_eq_card, hQcard]
  have hkerOdd : Odd (Nat.card ker) := by
    have := MonoidHom.not_dvd_card_ker_transferSylow Q hP
    exact Nat.not_even_iff_odd.1 fun h => this (even_iff_two_dvd.1 h)
  let M : Subgroup C := ker.map D.subtype
  have hMcard : Nat.card M = Nat.card ker := Subgroup.card_map_of_injective D.subtype_injective
  have hModd : Odd (Nat.card M) := by rw [hMcard]; exact hkerOdd
  have hkey : ∀ x ∈ D, Odd (orderOf x) → x ∈ M := by
    intro x hx hxo
    let x' : ↥D := ⟨x, hx⟩
    have h1 : x' ^ ker.index ∈ ker := Subgroup.pow_index_mem ker x'
    rw [hkerIdx] at h1
    obtain ⟨s, hs⟩ := hxo
    have hr : orderOf x' = 2 * s + 1 := by rw [Subgroup.orderOf_mk]; exact hs
    have h2 : x' = (x' ^ 2) ^ (s + 1) := by
      rw [← pow_mul, show 2 * (s + 1) = (2 * s + 1) + 1 by ring, pow_succ, ← hr, pow_orderOf_eq_one,
        one_mul]
    have h3 : x' ∈ ker := by rw [h2]; exact Subgroup.pow_mem _ h1 _
    exact ⟨x', h3, rfl⟩
  have hMn : M.Normal := ⟨fun m hm g => by
    have hmD : m ∈ D := Subgroup.map_subtype_le _ hm
    have hD' : g * m * g⁻¹ ∈ D := hDn.conj_mem m hmD g
    have hodd : Odd (orderOf m) := by
      have := orderOf_dvd_natCard (⟨m, hm⟩ : M)
      rw [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hModd this
    exact hkey _ hD' (by rw [orderOf_conj_eq']; exact hodd)⟩
  have hDle : D ≤ M ⊔ zpowers z := by
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥D) ∈ ker ⊔ (Q : Subgroup ↥D) := by
      rw [hc.sup_eq_top]; exact Subgroup.mem_top _
    have h2 := Subgroup.mem_map_of_mem D.subtype h1
    rw [Subgroup.map_sup] at h2
    have h3 : (Q : Subgroup ↥D).map D.subtype = zpowers z := by
      rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hzle]
    rw [h3] at h2
    exact h2
  exact ⟨M, Subgroup.map_subtype_le _, hMn, hModd, hDle⟩

end CFSG.GH74.GLS.Stage1.Thm4
