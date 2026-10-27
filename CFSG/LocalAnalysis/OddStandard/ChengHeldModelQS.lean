module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelSFacts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelCard

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

theorem mem_zpowers_of_pow_eq_one {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] {n : ℕ}
    (hn : 0 < n) {t u : Q} (ht : orderOf t = n) (hu : u ^ n = 1) : u ∈ zpowers t := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have h4 : t ^ n = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  by_contra hnot
  have hsub : insert u ((zpowers t : Set Q).toFinset) ⊆
      Finset.univ.filter (fun a : Q => a ^ n = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Set.mem_toFinset, SetLike.mem_coe] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | ha
    · exact hu
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h4, one_zpow]
  have hcard : ((zpowers t : Set Q).toFinset).card = n := by
    rw [Set.toFinset_card]
    simpa [Fintype.card_zpowers] using ht
  have h5 : (insert u ((zpowers t : Set Q).toFinset)).card = n + 1 := by
    rw [Finset.card_insert_of_notMem (by simpa using hnot), hcard]
  have h6 := Finset.card_le_card hsub
  have h7 := IsCyclic.card_pow_eq_one_le (α := Q) (n := n) hn
  omega

theorem Chart4.Q_inf_S_eq {α : ℕ} (c : Chart4 d α)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) : d.Q ⊓ d.S = zpowers c.t := by
  rw [d.Q_inf_S]
  refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 ?_) ?_).symm
  · exact ⟨⟨d.S_le_X c.t_mem.2, d.S_le_A c.t_mem.2⟩, d.Q_le_centralizer c.t_mem.1⟩
  · rw [hc, Nat.card_zpowers, c.orderOf_t]

theorem Chart2.Q_inf_S_eq (c : Chart2 d)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 2) : d.Q ⊓ d.S = zpowers d.q := by
  rw [d.Q_inf_S]
  refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 ?_) ?_).symm
  · exact ⟨⟨d.S_le_X c.mem.2.2.2.2.2.2, d.S_le_A c.mem.2.2.2.2.2.2⟩, d.q_cent⟩
  · rw [hc, Nat.card_zpowers, d.q_ord]

theorem Chart4.involutions_in_S {α : ℕ} (c : Chart4 d α) (h : Hyp G A) (hS : c.SFacts)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {i : G} (hi : i ∈ d.QS)
    (hi2 : i * i = 1) : i ∈ d.S := by
  have := d.Q_isCyclic h
  obtain ⟨u, hu, s, hs, rfl⟩ := d.mem_QS_iff.1 hi
  have hcomm : s * u = u * s := mem_centralizer_iff.1 (d.Q_le_centralizer_S hu) s hs
  have h1 : u ^ 2 * s ^ 2 = 1 := by
    have : u * s * (u * s) = u ^ 2 * s ^ 2 := by
      calc u * s * (u * s) = u * (s * u) * s := by group
        _ = u * (u * s) * s := by rw [hcomm]
        _ = u ^ 2 * s ^ 2 := by simp only [pow_two, mul_assoc]
    rw [← this]
    exact hi2
  have e : s ^ 2 = (u ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hs2 : s ^ 2 ∈ d.Q ⊓ d.S := ⟨by rw [e]; exact d.Q.inv_mem (pow_mem hu 2), pow_mem hs 2⟩
  rw [c.Q_inf_S_eq hc] at hs2
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hs2
  have ht4 : c.t ^ 4 = 1 := c.frame.t4
  obtain ⟨hn1, hn2⟩ := hS.no_root s hs
  have hs4 : (s ^ 2) ^ 2 = 1 := by
    have hr : c.t ^ k = c.t ^ (k % 4) := by
      rw [← zpow_mod_orderOf, c.orderOf_t]
      norm_num
    have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rw [← hk, hr]
    rcases hcases with h0 | h0 | h0 | h0
    · rw [h0]; simp
    · exfalso; apply hn1; rw [← hk, hr, h0]; simp
    · rw [h0]
      have : (c.t ^ (2 : ℤ)) ^ 2 = 1 := by
        rw [← zpow_natCast, ← zpow_mul]; norm_num; exact ht4
      exact this
    · exfalso; apply hn2; rw [← hk, hr, h0]
      have : c.t ^ (3 : ℤ) = c.t⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        calc c.t ^ (3 : ℤ) * c.t = c.t ^ 4 := by rw [← zpow_add_one]; norm_num
          _ = 1 := ht4
      exact this
  have hu4 : u ^ 4 = 1 := by
    have : (u ^ 2) ^ 2 = 1 := by
      have : ((u ^ 2)⁻¹) ^ 2 = 1 := by rw [← e]; exact hs4
      simpa using this
    simpa [← pow_mul] using this
  have hu' : (⟨u, hu⟩ : d.Q) ∈ zpowers (⟨c.t, c.t_mem.1⟩ : d.Q) :=
    mem_zpowers_of_pow_eq_one (n := 4) (by norm_num)
      (by rw [← c.orderOf_t]; exact (Subgroup.orderOf_coe (⟨c.t, c.t_mem.1⟩ : d.Q)).symm)
      (Subtype.ext (by simpa using hu4))
  have huS : u ∈ d.S := by
    have hz : u ∈ zpowers c.t := by
      obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hu'
      exact mem_zpowers_iff.2 ⟨m, by simpa using congrArg Subtype.val hm⟩
    exact (zpowers_le.2 c.t_mem.2) hz
  exact d.S.mul_mem huS hs

theorem Chart2.involutions_in_S (c : Chart2 d) (h : Hyp G A) (hS : c.SFacts)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 2) {i : G} (hi : i ∈ d.QS)
    (hi2 : i * i = 1) : i ∈ d.S := by
  have := d.Q_isCyclic h
  obtain ⟨u, hu, s, hs, rfl⟩ := d.mem_QS_iff.1 hi
  have hcomm : s * u = u * s := mem_centralizer_iff.1 (d.Q_le_centralizer_S hu) s hs
  have h1 : u ^ 2 * s ^ 2 = 1 := by
    have : u * s * (u * s) = u ^ 2 * s ^ 2 := by
      calc u * s * (u * s) = u * (s * u) * s := by group
        _ = u * (u * s) * s := by rw [hcomm]
        _ = u ^ 2 * s ^ 2 := by simp only [pow_two, mul_assoc]
    rw [← this]
    exact hi2
  have e : s ^ 2 = (u ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hs2 : s ^ 2 ∈ d.Q ⊓ d.S := ⟨by rw [e]; exact d.Q.inv_mem (pow_mem hu 2), pow_mem hs 2⟩
  rw [c.Q_inf_S_eq hc] at hs2
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hs2
  have hq2 : d.q ^ 2 = 1 := by rw [← d.q_ord]; exact pow_orderOf_eq_one d.q
  have hs1 : s ^ 2 = 1 := by
    have hr : d.q ^ k = d.q ^ (k % 2) := by
      rw [← zpow_mod_orderOf, d.q_ord]
      norm_num
    have hcases : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hcases with h0 | h0
    · rw [← hk, hr, h0]; simp
    · exfalso; apply hS.no_root_q s hs; rw [← hk, hr, h0]; simp
  have hu2 : u ^ 2 = 1 := by
    rw [hs1] at h1
    simpa using h1
  have hu' : (⟨u, hu⟩ : d.Q) ∈ zpowers (⟨d.q, d.q_mem_Q h⟩ : d.Q) :=
    mem_zpowers_of_pow_eq_one (n := 2) (by norm_num)
      (by rw [← d.q_ord]; exact (Subgroup.orderOf_coe (⟨d.q, d.q_mem_Q h⟩ : d.Q)).symm)
      (Subtype.ext (by simpa using hu2))
  have huS : u ∈ d.S := by
    have hz : u ∈ zpowers d.q := by
      obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hu'
      exact mem_zpowers_iff.2 ⟨m, by simpa using congrArg Subtype.val hm⟩
    exact (zpowers_le.2 c.mem.2.2.2.2.2.2) hz
  exact d.S.mul_mem huS hs

end CFSG.OddStandard.ChengHeld
