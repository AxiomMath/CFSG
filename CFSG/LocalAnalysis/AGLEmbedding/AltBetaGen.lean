module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import CFSG.Permutation.AlternatingAutomorphism.ThreeCycle

public section

namespace CFSG.AGLEmbedding

open Equiv Equiv.Perm Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem swap_mul_swap_rotate {a b c : α} (hab : a ≠ b) (hac : a ≠ c) :
    swap a b * swap b c = swap b c * swap c a := by
  rw [← swap_mul_swap_mul_swap hab hac]
  simp only [← mul_assoc, swap_mul_self, one_mul]

omit [Fintype α] in
theorem swap_mul_swap_eq_mul {x u v w : α} (hxu : x ≠ u) (hxv : x ≠ v) :
    swap u v * swap v w = swap x u * swap u v * (swap x v * swap v w) := by
  have h : swap x v = swap u v * swap x u * swap u v := by
    rw [swap_mul_swap_mul_swap hxu hxv, swap_comm]
  rw [h]
  simp only [mul_assoc, swap_mul_self_mul]

theorem support_swap_mul_swap_of_ne {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (swap a b * swap b c).support = {a, b, c} :=
  support_swap_mul_swap (by simp [hab, hac, hbc])

theorem isThreeCycle_swap_mul_swap {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (swap a b * swap b c).IsThreeCycle := by
  rw [← card_support_eq_three_iff, support_swap_mul_swap_of_ne hab hac hbc]
  exact card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩

theorem alternatingGroup_le_of_swap_mul_swap_mem {H : Subgroup (Perm α)}
    (h : ∀ a b c : α, a ≠ b → a ≠ c → b ≠ c → swap a b * swap b c ∈ H) :
    alternatingGroup α ≤ H := by
  rw [← closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro g hg
  have hg : g.IsThreeCycle := hg
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := card_eq_three.mp hg.card_support
  rcases AlternatingAutomorphism.eq_or_eq_inv_of_support_eq (isThreeCycle_swap_mul_swap hab hac hbc)
    hg (by rw [support_swap_mul_swap_of_ne hab hac hbc, hs]) with h1 | h1
  · rw [h1]
    exact h a b c hab hac hbc
  · rw [h1]
    exact inv_mem (h a b c hab hac hbc)

theorem swap_mul_swap_mem_of_notMem {H : Subgroup (Perm α)} {S : Finset α}
    (hS : ∀ g : Perm α, g.IsThreeCycle → _root_.Disjoint g.support S → g ∈ H) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : a ∉ S) (hb : b ∉ S) (hc : c ∉ S) :
    swap a b * swap b c ∈ H :=
  hS _ (isThreeCycle_swap_mul_swap hab hac hbc) (by
    rw [support_swap_mul_swap_of_ne hab hac hbc]
    simp [Finset.disjoint_insert_left, ha, hb, hc])

section Gen

variable {H : Subgroup (Perm α)} {S₁ S₂ : Finset α}
  (hS₁ : ∀ g : Perm α, g.IsThreeCycle → _root_.Disjoint g.support S₁ → g ∈ H)
  (hS₂ : ∀ g : Perm α, g.IsThreeCycle → _root_.Disjoint g.support S₂ → g ∈ H)
  (hd : _root_.Disjoint S₁ S₂) (h1 : 1 < #S₁) (h2 : 1 < #S₂)

include hS₁ hS₂ hd h1 h2 in
theorem swap_mul_swap_mem_of_mem {x a b : α} (hx1 : x ∉ S₁) (hx2 : x ∉ S₂) (ha : a ∈ S₂)
    (hb : b ∈ S₁) : swap x a * swap a b ∈ H := by
  obtain ⟨a', ha', ha'a⟩ := Finset.exists_mem_ne h2 a
  obtain ⟨b', hb', hb'b⟩ := Finset.exists_mem_ne h1 b
  have ha1 : a ∉ S₁ := Finset.disjoint_right.mp hd ha
  have ha'1 : a' ∉ S₁ := Finset.disjoint_right.mp hd ha'
  have hb2 : b ∉ S₂ := Finset.disjoint_left.mp hd hb
  have hb'2 : b' ∉ S₂ := Finset.disjoint_left.mp hd hb'
  have hxa : x ≠ a := fun h => hx2 (h ▸ ha)
  have hxa' : x ≠ a' := fun h => hx2 (h ▸ ha')
  have hxb : x ≠ b := fun h => hx1 (h ▸ hb)
  have hxb' : x ≠ b' := fun h => hx1 (h ▸ hb')
  have hab : a ≠ b := fun h => ha1 (h ▸ hb)
  have hab' : a ≠ b' := fun h => ha1 (h ▸ hb')
  have ha'b : a' ≠ b := fun h => ha'1 (h ▸ hb)
  have ha'b' : a' ≠ b' := fun h => ha'1 (h ▸ hb')
  have hu : swap x a * swap a a' ∈ H :=
    swap_mul_swap_mem_of_notMem hS₁ hxa hxa' (Ne.symm ha'a) hx1 ha1 ha'1
  have hσ : swap x b * swap b b' ∈ H :=
    swap_mul_swap_mem_of_notMem hS₂ hxb hxb' (Ne.symm hb'b) hx2 hb2 hb'2
  set σ := swap x b * swap b b' with hσdef
  have hσx : σ x = b := by
    rw [hσdef, Perm.mul_apply, swap_apply_of_ne_of_ne hxb hxb', swap_apply_left]
  have hσa : σ a = a := by
    rw [hσdef, Perm.mul_apply, swap_apply_of_ne_of_ne hab hab',
      swap_apply_of_ne_of_ne (Ne.symm hxa) hab]
  have hσa' : σ a' = a' := by
    rw [hσdef, Perm.mul_apply, swap_apply_of_ne_of_ne ha'b ha'b',
      swap_apply_of_ne_of_ne (Ne.symm hxa') ha'b]
  have hv : swap b a * swap a a' ∈ H := by
    have hconj : σ * (swap x a * swap a a') * σ⁻¹ = swap b a * swap a a' := by
      rw [show σ * (swap x a * swap a a') * σ⁻¹ = (σ * swap x a * σ⁻¹) * (σ * swap a a' * σ⁻¹) by
        group, ← swap_apply_apply, ← swap_apply_apply, hσx, hσa, hσa']
    rw [← hconj]
    exact mul_mem (mul_mem hσ hu) (inv_mem hσ)
  have hprod : swap x a * swap a b = swap x a * swap a a' * (swap b a * swap a a')⁻¹ := by
    rw [mul_inv_rev, swap_inv, swap_inv, mul_assoc, ← mul_assoc (swap a a'), swap_mul_self,
      one_mul, swap_comm b a]
  rw [hprod]
  exact mul_mem hu (inv_mem hv)

include hS₁ hS₂ hd h1 h2 in
theorem swap_mul_swap_mem_of_notMem_union {x a b : α} (hx1 : x ∉ S₁) (hx2 : x ∉ S₂)
    (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b) : swap x a * swap a b ∈ H := by
  by_cases ha1 : a ∈ S₁
  · by_cases hb2 : b ∈ S₂
    · exact swap_mul_swap_mem_of_mem hS₂ hS₁ hd.symm h2 h1 hx2 hx1 ha1 hb2
    · exact swap_mul_swap_mem_of_notMem hS₂ hxa hxb hab hx2 (Finset.disjoint_left.mp hd ha1) hb2
  · by_cases hb1 : b ∈ S₁
    · by_cases ha2 : a ∈ S₂
      · exact swap_mul_swap_mem_of_mem hS₁ hS₂ hd h1 h2 hx1 hx2 ha2 hb1
      · exact swap_mul_swap_mem_of_notMem hS₂ hxa hxb hab hx2 ha2 (Finset.disjoint_left.mp hd hb1)
    · exact swap_mul_swap_mem_of_notMem hS₁ hxa hxb hab hx1 ha1 hb1

include hS₁ hS₂ hd h1 h2 in
theorem alternatingGroup_le_of_disjoint {x : α} (hx1 : x ∉ S₁) (hx2 : x ∉ S₂) :
    alternatingGroup α ≤ H := by
  have hx : ∀ a b, x ≠ a → x ≠ b → a ≠ b → swap x a * swap a b ∈ H := fun a b hxa hxb hab =>
    swap_mul_swap_mem_of_notMem_union hS₁ hS₂ hd h1 h2 hx1 hx2 hxa hxb hab
  refine alternatingGroup_le_of_swap_mul_swap_mem fun u v w huv huw hvw => ?_
  by_cases hu : u = x
  · subst hu
    exact hx v w huv huw hvw
  by_cases hv : v = x
  · subst hv
    rw [swap_mul_swap_rotate huv huw]
    exact hx w u hvw (Ne.symm hu) (Ne.symm huw)
  by_cases hw : w = x
  · subst hw
    rw [swap_mul_swap_rotate huv huw, swap_mul_swap_rotate hvw (Ne.symm huv)]
    exact hx u v (Ne.symm huw) (Ne.symm hvw) huv
  · rw [swap_mul_swap_eq_mul (x := x) (Ne.symm hu) (Ne.symm hv)]
    exact mul_mem (hx u v (Ne.symm hu) (Ne.symm hv) huv) (hx v w (Ne.symm hv) (Ne.symm hw) hvw)

end Gen

theorem exists_isCycle_support_eq {s : Finset α} (hs : 2 ≤ #s) :
    ∃ c : Perm α, c.IsCycle ∧ c.support = s := by
  refine ⟨s.toList.formPerm, List.isCycle_formPerm s.nodup_toList (by rwa [Finset.length_toList]),
    ?_⟩
  rw [List.support_formPerm_of_nodup _ s.nodup_toList, Finset.toList_toFinset]
  intro x hx
  have := congrArg List.length hx
  rw [Finset.length_toList, List.length_singleton] at this
  omega

theorem exists_two_disjoint_cycles {p : ℕ} (hp : 2 ≤ p) (hcard : 2 * p + 1 ≤ Fintype.card α) :
    ∃ c₁ c₂ : Perm α, c₁.IsCycle ∧ c₂.IsCycle ∧ #c₁.support = p ∧ #c₂.support = p ∧
      _root_.Disjoint c₁.support c₂.support ∧ ∃ x, x ∉ c₁.support ∧ x ∉ c₂.support := by
  obtain ⟨s₁, -, hs₁⟩ := Finset.exists_subset_card_eq (s := (univ : Finset α)) (n := p)
    (by rw [card_univ]; omega)
  obtain ⟨s₂, hs₂u, hs₂⟩ := Finset.exists_subset_card_eq (s := univ \ s₁) (n := p)
    (by rw [card_sdiff_of_subset (subset_univ _), card_univ, hs₁]; omega)
  have hd : _root_.Disjoint s₁ s₂ :=
    Finset.disjoint_left.mpr fun a ha ha2 => (Finset.mem_sdiff.mp (hs₂u ha2)).2 ha
  obtain ⟨x, hx⟩ : (univ \ (s₁ ∪ s₂)).Nonempty := by
    rw [← Finset.card_pos, card_sdiff_of_subset (subset_univ _), card_univ,
      card_union_of_disjoint hd, hs₁, hs₂]
    omega
  obtain ⟨c₁, hc₁, rfl⟩ := exists_isCycle_support_eq (s := s₁) (by omega)
  obtain ⟨c₂, hc₂, rfl⟩ := exists_isCycle_support_eq (s := s₂) (by omega)
  simp only [Finset.mem_sdiff, mem_univ, mem_union, true_and, not_or] at hx
  exact ⟨c₁, c₂, hc₁, hc₂, hs₁, hs₂, hd, x, hx⟩

theorem mem_alternatingGroup_of_isCycle {c : Perm α} (hc : c.IsCycle) (hodd : Odd #c.support) :
    c ∈ alternatingGroup α := by
  rw [mem_alternatingGroup, hc.sign, hodd.neg_one_pow, neg_neg]

end CFSG.AGLEmbedding
