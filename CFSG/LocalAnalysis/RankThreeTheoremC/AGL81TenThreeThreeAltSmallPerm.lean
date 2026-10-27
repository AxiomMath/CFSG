module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open Equiv Equiv.Perm Subgroup

theorem cycleType_of_odd {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α ≤ 8)
    {σ : Perm α} (hodd : Odd (orderOf σ)) (h1 : σ ≠ 1) :
    σ.cycleType = {3} ∨ σ.cycleType = {5} ∨ σ.cycleType = {7} ∨ σ.cycleType = {3, 3} ∨
      σ.cycleType = {3, 5} := by
  have hodd' : ∀ a ∈ σ.cycleType, Odd a := fun a ha => hodd.of_dvd_nat (dvd_of_mem_cycleType ha)
  have h3 : ∀ a ∈ σ.cycleType, 3 ≤ a := fun a ha => by
    have h2 := two_le_of_mem_cycleType ha
    obtain ⟨k, hk⟩ := hodd' a ha
    omega
  have hsum : σ.cycleType.sum ≤ 8 := (sum_cycleType_le σ).trans hα
  have hcard : σ.cycleType.card * 3 ≤ σ.cycleType.sum := by
    simpa using Multiset.card_nsmul_le_sum h3
  have hne : σ.cycleType ≠ 0 := by rwa [Ne, cycleType_eq_zero]
  have hc : σ.cycleType.card = 1 ∨ σ.cycleType.card = 2 := by
    have : σ.cycleType.card ≠ 0 := by rwa [Ne, Multiset.card_eq_zero]
    omega
  rcases hc with hc | hc
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hc
    have ha3 := h3 a (by simp [ha])
    have hao := hodd' a (by simp [ha])
    have has : a ≤ 8 := by simpa [ha] using hsum
    obtain ⟨k, hk⟩ := hao
    have : a = 3 ∨ a = 5 ∨ a = 7 := by omega
    rcases this with rfl | rfl | rfl <;> simp [ha]
  · obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hc
    have ha3 := h3 a (by simp [hab])
    have hb3 := h3 b (by simp [hab])
    obtain ⟨k, hk⟩ := hodd' a (by simp [hab])
    obtain ⟨l, hl⟩ := hodd' b (by simp [hab])
    have hs : a + b ≤ 8 := by simpa [hab] using hsum
    have : (a = 3 ∧ b = 3) ∨ (a = 3 ∧ b = 5) ∨ (a = 5 ∧ b = 3) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [hab]
    · simp [hab]
    · right; right; right; right
      rw [hab, Multiset.pair_comm]

theorem two_mul_card_centralizer_inf_alt {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (h : ¬ centralizer {σ} ≤ alternatingGroup α) :
    2 * Nat.card ↥(centralizer {σ} ⊓ alternatingGroup α) = Nat.card ↥(centralizer {σ}) := by
  obtain ⟨t, ht, hta⟩ := SetLike.not_le_iff_exists.mp h
  have hs : sign t = -1 := by
    rcases Int.units_eq_one_or (sign t) with h1 | h1
    · exact absurd (mem_alternatingGroup.mpr h1) hta
    · exact h1
  set H := centralizer ({σ} : Set (Perm α))
  let f : ↥H →* ℤˣ := sign.comp H.subtype
  have hf : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨t, ht⟩, hs⟩
  have hker : f.ker = (alternatingGroup α).subgroupOf H := by
    ext x
    simp [f, mem_alternatingGroup, Subgroup.mem_subgroupOf]
  have h2 : f.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hmul := Subgroup.card_mul_index f.ker
  rw [h2, hker] at hmul
  have e1 : Nat.card ↥((alternatingGroup α).subgroupOf H) =
      Nat.card ↥(H ⊓ alternatingGroup α) := by
    have : (H ⊓ alternatingGroup α).subgroupOf H = (alternatingGroup α).subgroupOf H := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [← this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← e1, ← hmul, mul_comm]

theorem card_centralizer_inf_alt_cases {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) :
    (centralizer {σ} ≤ alternatingGroup α ∧
        Nat.card ↥(centralizer {σ} ⊓ alternatingGroup α) = Nat.card ↥(centralizer {σ})) ∨
      (¬ centralizer {σ} ≤ alternatingGroup α ∧
        2 * Nat.card ↥(centralizer {σ} ⊓ alternatingGroup α) = Nat.card ↥(centralizer {σ})) := by
  by_cases h : centralizer {σ} ≤ alternatingGroup α
  · exact Or.inl ⟨h, by rw [inf_eq_left.mpr h]⟩
  · exact Or.inr ⟨h, two_mul_card_centralizer_inf_alt h⟩

theorem odd_card_centralizer_alt_six {σ : Perm (Fin 6)} (hodd : Odd (orderOf σ)) (h1 : σ ≠ 1) :
    Odd (Nat.card ↥(centralizer {σ} ⊓ alternatingGroup (Fin 6))) := by
  have hc := nat_card_centralizer (g := σ)
  have hk := card_centralizer_inf_alt_cases σ
  have hs := sum_cycleType_le σ
  rw [centralizer_le_alternating_iff] at hk
  generalize Nat.card ↥(centralizer {σ} ⊓ alternatingGroup (Fin 6)) = x at hk ⊢
  generalize Nat.card ↥(centralizer {σ}) = C at hk hc
  rw [Nat.odd_iff]
  rcases cycleType_of_odd (by simp) hodd h1 with h | h | h | h | h <;> rw [h] at hk hc hs
  · simp [Nat.factorial] at hc hk
    omega
  · simp [Nat.factorial] at hc
    rcases hk with ⟨-, hk⟩ | ⟨-, hk⟩ <;> omega
  · simp at hs
  · simp [Nat.factorial] at hc
    rcases hk with ⟨⟨-, -, hk⟩, -⟩ | ⟨-, hk⟩
    · have := hk 3
      simp at this
    · omega
  · simp at hs

theorem not_eight_dvd_card_centralizer_alt_eight {σ : Perm (Fin 8)} (hodd : Odd (orderOf σ))
    (h1 : σ ≠ 1) : ¬ 8 ∣ Nat.card ↥(centralizer {σ} ⊓ alternatingGroup (Fin 8)) := by
  have hc := nat_card_centralizer (g := σ)
  have hk := card_centralizer_inf_alt_cases σ
  rw [centralizer_le_alternating_iff] at hk
  generalize Nat.card ↥(centralizer {σ} ⊓ alternatingGroup (Fin 8)) = x at hk ⊢
  generalize Nat.card ↥(centralizer {σ}) = C at hk hc
  rcases cycleType_of_odd (by simp) hodd h1 with h | h | h | h | h <;> rw [h] at hk hc <;>
    simp [Nat.factorial] at hc hk
  · omega
  · omega
  · rcases hk with ⟨-, hk⟩ | ⟨-, hk⟩ <;> omega
  · omega
  · rcases hk with ⟨-, hk⟩ | ⟨-, hk⟩ <;> omega

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
