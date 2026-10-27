module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.QuasithinUnique.Ch1

section Dihedral

variable {G : Type*} [Group G]

theorem involution_conj_zpow {a b : G} (ha : a * a = 1) (hb : b * b = 1) (i : ℤ) :
    a * (a * b) ^ i * a = (a * b) ^ (-i) := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h2 : a * (a * b) * a = (a * b)⁻¹ := by
    rw [mul_inv_rev, ha', hb', ← mul_assoc, ha, one_mul]
  have h3 := map_zpow (MulAut.conj a) (a * b) i
  simp only [MulAut.conj_apply, ha'] at h3
  rw [h2, inv_zpow'] at h3
  exact h3

theorem mem_closure_involutions_cases {a b : G} (ha : a * a = 1) (hb : b * b = 1) {g : G}
    (hg : g ∈ Subgroup.closure ({a, b} : Set G)) :
    (∃ i : ℤ, g = (a * b) ^ i) ∨ ∃ i : ℤ, g = (a * b) ^ i * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hc := involution_conj_zpow ha hb
  have hca : ∀ i : ℤ, a * (a * b) ^ i = (a * b) ^ (-i) * a := fun i => by
    calc a * (a * b) ^ i = (a * (a * b) ^ i * a) * a := by
          rw [mul_assoc (a * (a * b) ^ i), ha, mul_one]
      _ = (a * b) ^ (-i) * a := by rw [hc]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact Or.inr ⟨0, by rw [zpow_zero, one_mul]⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine Or.inr ⟨-1, ?_⟩
      rw [zpow_neg, zpow_one, mul_inv_rev, ha', hb', mul_assoc, ha, mul_one]
  | one => exact Or.inl ⟨0, (zpow_zero _).symm⟩
  | mul x y _ _ hx hy =>
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨i + j, (zpow_add _ _ _).symm⟩
    · exact Or.inr ⟨i + j, by rw [zpow_add, mul_assoc]⟩
    · refine Or.inr ⟨i - j, ?_⟩
      rw [mul_assoc, hca j, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
    · refine Or.inl ⟨i - j, ?_⟩
      calc (a * b) ^ i * a * ((a * b) ^ j * a)
          = (a * b) ^ i * (a * (a * b) ^ j) * a := by simp only [mul_assoc]
        _ = (a * b) ^ i * ((a * b) ^ (-j) * a) * a := by rw [hca j]
        _ = (a * b) ^ i * (a * b) ^ (-j) * (a * a) := by simp only [mul_assoc]
        _ = (a * b) ^ (i - j) := by rw [ha, mul_one, ← zpow_add, sub_eq_add_neg]
  | inv x _ hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl ⟨-i, (zpow_neg _ _).symm⟩
    · exact Or.inr ⟨i, by rw [mul_inv_rev, ha', ← zpow_neg, hca, neg_neg]⟩

theorem card_closure_involutions_le [Finite G] {a b : G} (ha : a * a = 1) (hb : b * b = 1) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ 2 * orderOf (a * b) := by
  set Q := Subgroup.closure ({a, b} : Set G) with hQ
  have haQ : a ∈ Q := Subgroup.subset_closure (by simp)
  have hbQ : b ∈ Q := Subgroup.subset_closure (by simp)
  have hN : Subgroup.zpowers (a * b) ≤ Q := Subgroup.zpowers_le.2 (mul_mem haQ hbQ)
  let f : Subgroup.zpowers (a * b) × Bool → Q := fun p =>
    if p.2 then ⟨(p.1 : G) * a, mul_mem (hN p.1.2) haQ⟩ else ⟨(p.1 : G), hN p.1.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    rcases mem_closure_involutions_cases ha hb hg with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨(⟨(a * b) ^ i, i, rfl⟩, false), rfl⟩
    · exact ⟨(⟨(a * b) ^ i, i, rfl⟩, true), rfl⟩
  calc Nat.card Q ≤ Nat.card (Subgroup.zpowers (a * b) × Bool) :=
        Nat.card_le_card_of_surjective f hf
    _ = 2 * orderOf (a * b) := by
        have hb2 : Nat.card Bool = 2 := by simp
        rw [Nat.card_prod, Nat.card_zpowers, hb2]
        ring

theorem odd_orderOf_of_mem_closure {A : Type*} [Group A] (π : G →* A) {a b u z : G}
    (ha : a * a = 1) (hb : b * b = 1) (hu : u * u = 1)
    (hr : orderOf (π (a * b)) = 4) (hnot : π a ∉ Subgroup.zpowers (π (a * b)))
    (hπu : π u = π (a * b) ^ 2) (hu' : u ∈ Subgroup.closure ({a, b} : Set G))
    (hz : z ∈ Subgroup.closure ({a, b} : Set G)) (hz1 : π z = 1) : Odd (orderOf z) := by
  set x := π (a * b) with hx
  have hrefl : ∀ (g : G) (i : ℤ) (c : A), g = (a * b) ^ i * a → π g = c →
      c ∈ Subgroup.zpowers x → False := by
    intro g i c hg hgc hc
    apply hnot
    have h1 : x ^ i * π a = c := by rw [← hgc, hg, map_mul, map_zpow]
    have h2 : π a = (x ^ i)⁻¹ * c := eq_inv_mul_of_mul_eq h1
    rw [h2, ← zpow_neg]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem_zpowers _ _) hc
  obtain ⟨i, hi⟩ : ∃ i : ℤ, z = (a * b) ^ i := by
    rcases mem_closure_involutions_cases ha hb hz with h | ⟨i, hi⟩
    · exact h
    · exact (hrefl z i 1 hi hz1 (Subgroup.one_mem _)).elim
  obtain ⟨j, hj⟩ : ∃ j : ℤ, u = (a * b) ^ j := by
    rcases mem_closure_involutions_cases ha hb hu' with h | ⟨j, hj⟩
    · exact h
    · exact (hrefl u j (x ^ 2) hj hπu (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2)).elim
  have h4i : (4 : ℤ) ∣ i := by
    have h1 : x ^ i = 1 := by rw [hx, ← map_zpow, ← hi, hz1]
    have := orderOf_dvd_iff_zpow_eq_one.2 h1
    rwa [hr, Nat.cast_ofNat] at this
  have hxj : x ^ j = x ^ (2 : ℤ) := by
    rw [zpow_ofNat, hx, ← map_zpow, ← hj]
    exact hπu
  have h4j : (4 : ℤ) ∣ j - 2 := by
    have h1 : x ^ (j - 2) = 1 := by rw [zpow_sub, hxj]; exact mul_inv_cancel _
    have := orderOf_dvd_iff_zpow_eq_one.2 h1
    rwa [hr, Nat.cast_ofNat] at this
  obtain ⟨s, hs⟩ := h4i
  obtain ⟨t, ht⟩ := h4j
  have hu2 : (a * b) ^ (2 * j) = 1 := by
    rw [two_mul, zpow_add, ← hj]
    exact hu
  have h3 : (a * b) ^ (4 * (2 * t + 1)) = 1 := by
    have : 2 * j = 4 * (2 * t + 1) := by omega
    rwa [this] at hu2
  have hz3 : z ^ (2 * t + 1) = 1 := by
    rw [hi, ← zpow_mul, hs, show 4 * s * (2 * t + 1) = (4 * (2 * t + 1)) * s by ring, zpow_mul, h3,
      one_zpow]
  have hdvd : (orderOf z : ℤ) ∣ 2 * t + 1 := orderOf_dvd_iff_zpow_eq_one.2 hz3
  have hdvd' : orderOf z ∣ (2 * t + 1).natAbs := Int.natCast_dvd.1 hdvd
  exact Odd.of_dvd_nat (Int.natAbs_odd.2 ⟨t, rfl⟩) hdvd'

end Dihedral

end CFSG.QuasithinUnique.Ch1
