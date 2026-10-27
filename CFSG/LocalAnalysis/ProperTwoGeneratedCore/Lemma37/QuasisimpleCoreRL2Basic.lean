module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Quat
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePCases

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G]

@[expose] def qPowSubgroup (Q : Subgroup G) (g : G) (hg : ∀ q ∈ Q, q * g = g * q) :
    Subgroup G where
  carrier := {x | ∃ q ∈ Q, ∃ l : ℤ, x = q * g ^ l}
  one_mem' := ⟨1, Q.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨q, hq, l, rfl⟩ ⟨q', hq', l', rfl⟩
    refine ⟨q * q', Q.mul_mem hq hq', l + l', ?_⟩
    have h : g ^ l * q' = q' * g ^ l := ((show Commute q' g from hg q' hq').zpow_right l).eq.symm
    rw [zpow_add, show q * g ^ l * (q' * g ^ l') = q * (g ^ l * q') * g ^ l' by group, h]
    group
  inv_mem' := by
    rintro _ ⟨q, hq, l, rfl⟩
    refine ⟨q⁻¹, Q.inv_mem hq, -l, ?_⟩
    have h : g ^ (-l) * q⁻¹ = q⁻¹ * g ^ (-l) :=
      ((show Commute q⁻¹ g from (show Commute q g from hg q hq).inv_left).zpow_right (-l)).eq.symm
    rw [mul_inv_rev, ← zpow_neg, h]

@[expose] def twoCosets (A : Subgroup G) (y : G) (hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    (hyy : y * y ∈ A) : Subgroup G where
  carrier := {x | x ∈ A ∨ x * y⁻¹ ∈ A}
  one_mem' := Or.inl A.one_mem
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (A.mul_mem ha hb)
    · exact Or.inr (by rw [mul_assoc]; exact A.mul_mem ha hb)
    · refine Or.inr ?_
      rw [show a * b * y⁻¹ = (a * y⁻¹) * (y * b * y⁻¹) by group]
      exact A.mul_mem ha (hyA b hb)
    · refine Or.inl ?_
      rw [show a * b = (a * y⁻¹) * (y * (b * y⁻¹) * y⁻¹) * (y * y) by group]
      exact A.mul_mem (A.mul_mem ha (hyA _ hb)) hyy
  inv_mem' := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (A.inv_mem ha)
    · refine Or.inr ?_
      rw [show a⁻¹ * y⁻¹ = (y * (a * y⁻¹) * y⁻¹ * (y * y))⁻¹ by group]
      exact A.inv_mem (A.mul_mem (hyA _ ha) hyy)

theorem mem_twoCosets {A : Subgroup G} {y : G} {hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A}
    {hyy : y * y ∈ A} {x : G} : x ∈ twoCosets A y hyA hyy ↔ x ∈ A ∨ x * y⁻¹ ∈ A :=
  Iff.rfl

namespace PartC

variable {T Q P₁ : Subgroup G} {e u y : G}

theorem mem_zpowers_centralElt_iff (hc : PartC T Q P₁ e u) {x : G} :
    x ∈ Subgroup.zpowers e ↔ x = 1 ∨ x = e := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, hc.order]
    have h0 : 0 ≤ k % ((2 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h1 : k % ((2 : ℕ) : ℤ) < 2 := Int.emod_lt_of_pos _ (by norm_num)
    obtain h | h : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (h | h) <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers e

theorem conj_eq_of_mem_zpowers_centralElt (hc : PartC T Q P₁ e u) {x : G}
    (hx : x ∈ Subgroup.zpowers e) (a : G) : a⁻¹ * x * a = x := by
  rcases hc.mem_zpowers_centralElt_iff.mp hx with h | h <;> rw [h]
  · group
  · rw [mul_assoc, ← hc.commute_centralElt a, inv_mul_cancel_left]

theorem zpowers_centralElt_le_left (hc : PartC T Q P₁ e u) : Subgroup.zpowers e ≤ Q :=
  Subgroup.zpowers_le.mpr hc.mem_left

theorem comm_right_of_isCyclic (hcyc : IsCyclic P₁) {p p' : G} (hp : p ∈ P₁) (hp' : p' ∈ P₁) :
    p * p' = p' * p := by
  let : CommGroup P₁ := IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨p, hp⟩ : P₁) ⟨p', hp'⟩)

theorem eq_of_mem_right_of_isCyclic [Finite G] (hc : PartC T Q P₁ e u) (hcyc : IsCyclic P₁) {x : G}
    (hx : x ∈ P₁) (hxx : x * x = e) : x = u ∨ x = u * e := by
  have heq : Subgroup.zpowers (⟨x, hx⟩ : P₁) = Subgroup.zpowers ⟨u, hc.self_mem⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc.orderOf_eq_four_of_mul_self hxx,
      hc.orderOf_eq_four_of_mul_self hc.sq]
  have hmem : (⟨x, hx⟩ : P₁) ∈ Subgroup.zpowers (⟨u, hc.self_mem⟩ : P₁) :=
    heq ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hxu : x ∈ Subgroup.zpowers u := ⟨k, by simpa using congrArg Subtype.val hk⟩
  exact hc.eq_of_mem_zpowers_of_mul_self hc.sq hxu hxx

theorem exists_generator [Finite G] (hc : PartC T Q P₁ e u) (hcyc : IsCyclic P₁) :
    ∃ c : G, ∃ n : ℕ, Subgroup.zpowers c = P₁ ∧ orderOf c = 2 ^ n ∧ 2 ≤ n ∧
      c ^ 2 ^ (n - 1) = e := by
  obtain ⟨c, hcP⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top P₁).mp hcyc
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hc.isPGroup.to_le hc.right_le)
  have hco : orderOf c = 2 ^ n := by rw [← Nat.card_zpowers, hcP, hn]
  have hu : orderOf u ∣ orderOf c :=
    orderOf_dvd_of_mem_zpowers (by rw [hcP]; exact hc.self_mem)
  rw [hc.orderOf_eq_four_of_mul_self hc.sq, hco, show (4 : ℕ) = 2 ^ 2 by norm_num] at hu
  have hn2 : 2 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hu
  have hmem : c ^ 2 ^ (n - 1) ∈ P₁ := by
    rw [← hcP]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _
  refine ⟨c, n, hcP, hco, hn2, hc.unique _ hmem ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) (by rw [hco]; exact pow_dvd_pow 2 (Nat.sub_le n 1)),
    hco, show n = n - 1 + 1 by omega, pow_succ, Nat.add_sub_cancel,
    Nat.mul_div_cancel_left _ (by positivity)]

theorem zpowers_self_eq_right [Finite G] (hc : PartC T Q P₁ e u) {c : G}
    (hcP : Subgroup.zpowers c = P₁) (hco : orderOf c = 2 ^ 2) : Subgroup.zpowers u = P₁ := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc.self_mem) ?_
  rw [← hcP, Nat.card_zpowers, Nat.card_zpowers, hco, hc.orderOf_eq_four_of_mul_self hc.sq]
  norm_num

theorem fix_of_not_mem (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) {v : G}
    (hfix : ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
      w = 1 ∨ w = e ∨ w = v ∨ w = v * e) {t : G} (htT : t ∈ T) (ht : t ∉ Q ⊔ P₁) {w : G}
    (hw : w ∈ Q) (htw : t * w * t⁻¹ = w ∨ t * w * t⁻¹ = w * e) :
    w = 1 ∨ w = e ∨ w = v ∨ w = v * e := by
  obtain ⟨q, hq, p, hp, hqp⟩ := hc.mem_sup_iff.mp (hc.inv_mul_mem y hyT t htT hy ht)
  have hs : q * p * w * (q * p)⁻¹ = w ∨ q * p * w * (q * p)⁻¹ = w * e := by
    have h1 : q * p * w * (q * p)⁻¹ = q * w * q⁻¹ := by
      calc q * p * w * (q * p)⁻¹ = q * (p * w * p⁻¹) * q⁻¹ := by group
        _ = q * w * q⁻¹ := by rw [← hc.commute w hw p hp, mul_inv_cancel_right]
    rw [h1]
    rcases hc.comm_or_anticomm hq hw with h | h
    · left
      rw [h, mul_inv_cancel_right]
    · right
      rw [h, mul_assoc w q e, hc.commute_centralElt q]
      group
  have hty : t = y * (q * p) := by rw [hqp]; group
  refine hfix w hw ?_
  rcases hs with h | h <;> rcases htw with h' | h' <;> rw [hty] at h'
  · left
    rwa [show y * (q * p) * w * (y * (q * p))⁻¹ = y * (q * p * w * (q * p)⁻¹) * y⁻¹ by group,
      h] at h'
  · right
    rwa [show y * (q * p) * w * (y * (q * p))⁻¹ = y * (q * p * w * (q * p)⁻¹) * y⁻¹ by group,
      h] at h'
  · right
    rw [show y * (q * p) * w * (y * (q * p))⁻¹ = y * (q * p * w * (q * p)⁻¹) * y⁻¹ by group,
      h, hc.conj_mul_centralElt] at h'
    calc y * w * y⁻¹ = y * w * y⁻¹ * e * e := (hc.mul_centralElt_mul_centralElt _).symm
      _ = w * e := by rw [h']
  · left
    rw [show y * (q * p) * w * (y * (q * p))⁻¹ = y * (q * p * w * (q * p)⁻¹) * y⁻¹ by group,
      h, hc.conj_mul_centralElt] at h'
    exact mul_right_cancel h'

theorem mul_self_eq_of_not_isCyclic [Finite G] (hc : PartC T Q P₁ e u) (hcyc : IsCyclic P₁)
    (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁)
    (hP : ¬ IsCyclic (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) {w : G}
    (hw : w ∈ P₁ ⊔ Subgroup.zpowers y) (hw₁ : w ∉ P₁) : w * w = e := by
  obtain ⟨c, n, hcP, hco, hn, -⟩ := hc.exists_generator hcyc
  have hcardP : Nat.card (P₁ ⊔ Subgroup.zpowers y : Subgroup G) = 2 ^ (n + 1) := by
    rw [hc.card_sup_zpowers hyT hy hyy, ← hcP, Nat.card_zpowers, hco, pow_succ, mul_comm]
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    have hww : w * w ∈ P₁ := hc.mul_self_mem_right hyT hyy hw
    have hw8 : w ^ 2 ^ (2 + 1) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← Subgroup.orderOf_mk w hw, ← hcardP]
      exact orderOf_dvd_natCard _
    by_cases h4 : w ^ 2 ^ 2 = 1
    · have h4' : w * w * (w * w) = 1 := by
        rw [← h4, show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, pow_two]
      rcases hc.eq_of_mem_right_of_mul_self hww h4' with h | h
      · exfalso
        have hw1 : w ≠ 1 := fun h1 => hw₁ (h1 ▸ P₁.one_mem)
        have h2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact h) hw1
        exact hw₁ (hc.eq_of_mem_sup_zpowers hyT hy hyy hw h2 ▸ hc.mem_right)
      · exact h
    · exfalso
      have hord : orderOf w = 2 ^ (2 + 1) := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime_pow h4 hw8
      apply hP
      rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
      refine ⟨w, Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw) ?_⟩
      rw [Nat.card_zpowers, hord, hcardP]
  · obtain ⟨k, -, hcard, ⟨φ⟩⟩ := hc.quaternion_of_unique (hc.sup_zpowers_le hyT)
      (fun x hx hx2 => hc.eq_of_mem_sup_zpowers hyT hy hyy hx hx2) hP
    obtain rfl : k = n + 1 := by
      rw [hcardP] at hcard
      exact (Nat.pow_right_injective le_rfl hcard).symm
    have : NeZero (2 ^ (n + 1 - 2)) := ⟨by positivity⟩
    have hc'o : orderOf (quatGen φ) = 2 ^ n := by
      rw [quatGen, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one,
        ← pow_succ']
      congr 1
      omega
    have hcc' : c ∈ Subgroup.zpowers (quatGen φ) := by
      rcases hc.mem_sup_zpowers_cases φ hyT hy hyy
          (Subgroup.mem_sup_left (hcP ▸ Subgroup.mem_zpowers c)) with ⟨k, hk⟩ | ⟨hcc, -⟩
      · rw [hk]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      · exfalso
        have h4 := hc.orderOf_eq_four_of_mul_self hcc
        have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
        rw [hco] at h4
        omega
    have hP₁ : P₁ = Subgroup.zpowers (quatGen φ) := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · intro x hx
        rw [← hcP] at hx
        exact Subgroup.zpowers_le.mpr hcc' hx
      · rw [Nat.card_zpowers, hc'o, ← hcP, Nat.card_zpowers, hco]
    rcases hc.mem_sup_zpowers_cases φ hyT hy hyy hw with ⟨k, hk⟩ | ⟨hww, -⟩
    · exact absurd (by rw [hP₁, hk]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) hw₁
    · exact hww

theorem mul_self_eq_and_inv_of_not_isCyclic [Finite G] (hc : PartC T Q P₁ e u)
    (hcyc : IsCyclic P₁) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁)
    (hP : ¬ IsCyclic (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) :
    y * y = e ∧ ∀ p ∈ P₁, y * p * y⁻¹ = p⁻¹ := by
  have hyP : y ∈ P₁ ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hy₁ : y ∉ P₁ := fun h => hy (Subgroup.mem_sup_right h)
  have hyy' := hc.mul_self_eq_of_not_isCyclic hcyc hyT hy hyy hP hyP hy₁
  refine ⟨hyy', fun p hp => ?_⟩
  have hpy := hc.mul_self_eq_of_not_isCyclic hcyc hyT hy hyy hP
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) hyP)
    (fun h => hy₁ (by simpa using P₁.mul_mem (P₁.inv_mem hp) h))
  calc y * p * y⁻¹ = p⁻¹ * (p * y * (p * y)) * (y * y)⁻¹ := by group
    _ = p⁻¹ := by rw [hpy, hyy', mul_inv_cancel_right]

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
