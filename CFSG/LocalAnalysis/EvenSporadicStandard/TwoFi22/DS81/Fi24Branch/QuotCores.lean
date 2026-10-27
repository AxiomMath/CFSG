module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CSetup

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {C : Type} [Group C] [Finite C]

theorem pCore_Qt_eq_bot {c : CInv C} (hC : CCore c) : CFSG.pCore 2 c.Qt = ⊥ := by
  classical
  set P := CFSG.pCore 2 c.Qt with hPdef
  have hPnormal : P.Normal := CFSG.pCore_normal
  have hPp : IsPGroup 2 ↥P := CFSG.pCore_isPGroup
  have hPhnormal : (P.comap c.qmap).Normal := hPnormal.comap c.qmap
  have hPhp : IsPGroup 2 ↥(P.comap c.qmap) := c.isPGroup_comap hPp
  have hle : P.comap c.qmap ≤ zpowers c.z := hC.two _ hPhnormal hPhp
  have hbar : c.bar (P.comap c.qmap) = P := c.bar_comap P
  have hbar_le : c.bar (P.comap c.qmap) ≤ c.bar (zpowers c.z) := c.bar_mono hle
  have hbar_z : c.bar (zpowers c.z) = ⊥ := by
    change (zpowers c.z).map c.qmap = ⊥
    rw [eq_bot_iff]
    rintro y ⟨x, hx, rfl⟩
    show c.qmap x = 1
    exact c.qmap_eq_one_iff.mpr hx
  rw [← hbar]
  exact le_bot_iff.mp (hbar_le.trans (le_of_eq hbar_z))

theorem pPrimeCore_Qt_eq_bot {c : CInv C} (hC : CCore c) : CFSG.pPrimeCore 2 c.Qt = ⊥ := by
  classical
  set Q := CFSG.pPrimeCore 2 c.Qt with hQdef
  have hQnormal : Q.Normal := CFSG.pPrimeCore_normal
  have hQcop : Nat.Coprime 2 (Nat.card ↥Q) := CFSG.pPrimeCore_coprime_card
  have hQodd : Odd (Nat.card ↥Q) := hQcop.odd_of_left
  let Qh : Subgroup C := Q.comap c.qmap
  have hQhnormal : Qh.Normal := hQnormal.comap c.qmap
  have hQhcard : Nat.card ↥Qh = 2 * Nat.card ↥Q := c.card_comap Q
  have hz_le : zpowers c.z ≤ Qh := by
    intro x hx
    show c.qmap x ∈ Q
    rw [c.qmap_eq_one_iff.mpr hx]
    exact Q.one_mem
  let N : Subgroup Qh := (zpowers c.z).subgroupOf Qh
  have hNnormal : N.Normal := inferInstance
  have hNcard : Nat.card ↥N = 2 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hz_le).toEquiv
    rw [h, c.card_zpowers]
  have hNindex : N.index = Nat.card ↥Q := by
    have hcm := N.card_mul_index
    rw [hNcard, hQhcard] at hcm
    exact Nat.mul_left_cancel (by norm_num) hcm
  have hNcop : Nat.Coprime (Nat.card ↥N) N.index := by
    rw [hNcard, hNindex]; exact hQcop
  haveI := hNnormal
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime (G := Qh) (N := N) hNcop
  have hHcard : Nat.card ↥H = Nat.card ↥Q := by
    have hcm := hH.card_mul_card
    rw [hNcard, hQhcard] at hcm
    exact Nat.mul_left_cancel (by norm_num) hcm
  let O' : Subgroup C := H.map Qh.subtype
  have hO'le : O' ≤ Qh := by
    intro o ho
    change o ∈ H.map Qh.subtype at ho
    rw [Subgroup.mem_map] at ho
    obtain ⟨h, hh, rfl⟩ := ho
    exact h.2
  have hO'card : Nat.card ↥O' = Nat.card ↥Q := by
    have h1 : Nat.card ↥O' = Nat.card ↥H := Subgroup.card_subtype Qh H
    rw [h1, hHcard]
  have hO'odd : Odd (Nat.card ↥O') := by
    rw [hO'card]; exact hQodd
  have hO'normal : O'.Normal := by
    refine ⟨fun o ho g => ?_⟩
    have hgQh : g * o * g⁻¹ ∈ Qh := hQhnormal.conj_mem o (hO'le ho) g
    let xq : Qh := ⟨g * o * g⁻¹, hgQh⟩
    obtain ⟨⟨n, h⟩, hnh⟩ := hH.2 xq
    have hnh' : (n : Qh) * (h : Qh) = xq := hnh
    by_cases hn1 : (n : Qh) = 1
    · have hxq_eq : xq = (h : Qh) := by rw [← hnh', hn1, one_mul]
      have hval : g * o * g⁻¹ = (h : C) := by
        have := congrArg (fun y : Qh => (y : C)) hxq_eq
        simpa [xq] using this
      rw [hval]
      exact Subgroup.mem_map.mpr ⟨h, h.2, rfl⟩
    · exfalso
      have hcomm : Commute (n : Qh) (h : Qh) := by
        have hcenter : N ≤ Subgroup.center Qh := by
          intro m hm
          rw [Subgroup.mem_center_iff]
          intro y
          have hz : (m : C) ∈ zpowers c.z := Subgroup.mem_subgroupOf.mp hm
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
          apply Subtype.ext
          show (y : C) * (m : C) = (m : C) * (y : C)
          rw [← hk]
          exact (Commute.zpow_left (c.central (y : C)).symm k).symm
        exact (Subgroup.mem_center_iff.mp (hcenter n.2) (h : Qh)).symm
      have hn_order : orderOf (n : Qh) = 2 := by
        have hdvd : orderOf (n : Qh) ∣ 2 := by
          have h := Subgroup.orderOf_dvd_natCard N n.2
          rwa [hNcard] at h
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact absurd (orderOf_eq_one_iff.mp h1) hn1
        · exact h2
      have hoddh : Odd (orderOf (h : Qh)) := by
        have hdvd : orderOf (h : Qh) ∣ Nat.card ↥Q := by
          have h := Subgroup.orderOf_dvd_natCard H h.2
          rwa [hHcard] at h
        exact hQodd.of_dvd_nat hdvd
      have hcop : Nat.Coprime (orderOf (n : Qh)) (orderOf (h : Qh)) := by
        rw [hn_order]
        exact Nat.coprime_two_left.mpr hoddh
      have hparity : orderOf ((n : Qh) * (h : Qh)) = 2 * orderOf (h : Qh) := by
        rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hn_order]
      have hxq_order : orderOf xq = orderOf o := by
        rw [← Subgroup.orderOf_coe xq]
        show orderOf (g * o * g⁻¹) = orderOf o
        exact (SemiconjBy.orderOf_eq g (by
          show g * o = (g * o * g⁻¹) * g
          group)).symm
      have ho_odd : Odd (orderOf o) :=
        hO'odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O' ho)
      have hEven : Even (orderOf o) := by
        rw [← hxq_order, ← hnh', hparity]
        exact ⟨orderOf (h : Qh), by ring⟩
      exact (Nat.not_even_iff_odd.mpr ho_odd) hEven
  have hO'bot : O' = ⊥ := hC.odd O' hO'normal hO'odd
  have hQcard : Nat.card ↥Q = 1 := by
    rw [← hO'card, hO'bot]
    simp
  exact Subgroup.eq_bot_of_card_eq Q hQcard

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
