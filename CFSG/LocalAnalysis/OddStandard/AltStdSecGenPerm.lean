module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecPerm

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup

section Cyc3

variable {α : Type*} [DecidableEq α]

theorem cyc3_inv_of_ne {x y z : α} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    (cyc3 x y z)⁻¹ = cyc3 x z y := by
  simp only [cyc3, mul_inv_rev, swap_inv]
  ext i
  simp only [Perm.mul_apply, swap_apply_def]
  grind

theorem cyc3_rotate_of_ne {x y z : α} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    cyc3 x y z = cyc3 y z x := by
  ext i
  simp only [cyc3, Perm.mul_apply, swap_apply_def]
  grind

theorem cyc3_conj (g : Perm α) (x y z : α) :
    g * cyc3 x y z * g⁻¹ = cyc3 (g x) (g y) (g z) := by
  simp only [cyc3, swap_apply_apply]
  group

end Cyc3

section Alt

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem altSub_mono {S T : Finset α} (h : S ⊆ T) : altSub S ≤ altSub T := by
  intro g hg
  obtain ⟨hs, hfix⟩ := mem_altSub.1 hg
  exact mem_altSub.2 ⟨hs, fun i hi => hfix i fun hiS => hi (h hiS)⟩

theorem altSub_le_of_cyc3 {T : Finset α} {H : Subgroup (Perm α)}
    (h : ∀ x y z, x ∈ T → y ∈ T → z ∈ T → x ≠ y → y ≠ z → x ≠ z → cyc3 x y z ∈ H) :
    altSub T ≤ H := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := hg
  obtain ⟨k', rfl⟩ := hk
  show ((alternatingGroup.ofSubtype T k' : alternatingGroup α) : Perm α) ∈ H
  rw [alternatingGroup.coe_ofSubtype]
  have hmem : (k'.1 : Perm ↥T) ∈ Subgroup.closure {σ : Perm ↥T | σ.IsThreeCycle} := by
    rw [Perm.closure_three_cycles_eq_alternating]; exact k'.2
  refine Subgroup.closure_induction (p := fun σ _ => Perm.ofSubtype σ ∈ H) ?_ ?_ ?_ ?_ hmem
  · intro σ hσ
    have hne : σ.support.Nonempty := by
      rw [← Finset.card_pos, hσ.card_support]; norm_num
    obtain ⟨a, ha⟩ := hne
    have heq := (hσ.eq_swap_mul_swap_iff_mem_support (a := a)).2 ha
    have hnd := (hσ.nodup_iff_mem_support (a := a)).2 ha
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true,
      List.mem_nil_iff, or_false] at hnd
    have h1 : a ≠ σ a := fun e => (Perm.mem_support.1 ha) e.symm
    have h2 : σ a ≠ σ (σ a) := fun e => h1 (σ.injective e)
    have h3 : a ≠ σ (σ a) := hnd.1.2
    rw [heq, map_mul, Perm.ofSubtype_swap_eq, Perm.ofSubtype_swap_eq]
    exact h _ _ _ (a.2) (σ a).2 (σ (σ a)).2
      (fun e => h1 (Subtype.ext e)) (fun e => h2 (Subtype.ext e)) (fun e => h3 (Subtype.ext e))
  · simp
  · intro x y _ _ hx hy
    rw [map_mul]; exact mul_mem hx hy
  · intro x _ hx
    rw [map_inv]; exact inv_mem hx

section Gen

theorem cyc3_mem_sup_aux {S T : Finset α} (hI : 3 ≤ (S ∩ T).card) {x y w : α} (hxS : x ∈ S)
    (hxT : x ∉ T) (hyT : y ∈ T) (hyS : y ∉ S) (hwS : w ∈ S) (hxw : x ≠ w) (hwy : w ≠ y) :
    cyc3 x w y ∈ altSub S ⊔ altSub T := by
  have hcard : 1 < ((S ∩ T).erase w).card := by
    have := Finset.pred_card_le_card_erase (s := S ∩ T) (a := w)
    omega
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.1 hcard
  rw [Finset.mem_erase, Finset.mem_inter] at hb hc
  obtain ⟨hbw, hbS, hbT⟩ := hb
  obtain ⟨hcw, hcS, hcT⟩ := hc
  have hby : b ≠ y := fun e => hyS (e ▸ hbS)
  have hyc : y ≠ c := fun e => hyS (e ▸ hcS)
  have hxb : x ≠ b := fun e => hxT (e ▸ hbT)
  have hxc : x ≠ c := fun e => hxT (e ▸ hcT)
  have hg : cyc3 b y c ∈ altSub T := cyc3_mem_altSub hbT hyT hcT hby hyc hbc
  have hc0 : cyc3 x w b ∈ altSub S := cyc3_mem_altSub hxS hwS hbS hxw (Ne.symm hbw) hxb
  have hconj := cyc3_conj (cyc3 b y c) x w b
  have hxy : x ≠ y := fun e => hyS (e ▸ hxS)
  have e1 : cyc3 b y c x = x := cyc3_apply_of_ne hxb hxy hxc
  have e2 : cyc3 b y c w = w := cyc3_apply_of_ne (Ne.symm hbw) hwy (Ne.symm hcw)
  have e3 : cyc3 b y c b = y := cyc3_apply_left hby hbc
  rw [e1, e2, e3] at hconj
  rw [← hconj]
  have hgs : cyc3 b y c ∈ altSub S ⊔ altSub T := Subgroup.mem_sup_right hg
  have hc0s : cyc3 x w b ∈ altSub S ⊔ altSub T := Subgroup.mem_sup_left hc0
  exact mul_mem (mul_mem hgs hc0s) (inv_mem hgs)

theorem cyc3_mem_sup_mixed {S T : Finset α} (hI : 3 ≤ (S ∩ T).card) {x y w : α} (hxS : x ∈ S)
    (hxT : x ∉ T) (hyT : y ∈ T) (hyS : y ∉ S) (hw : w ∈ S ∪ T) (hxw : x ≠ w) (hwy : w ≠ y) :
    cyc3 x y w ∈ altSub S ⊔ altSub T := by
  have hxy : x ≠ y := fun e => hyS (e ▸ hxS)
  by_cases hwS : w ∈ S
  · have h := cyc3_mem_sup_aux hI hxS hxT hyT hyS hwS hxw hwy
    rw [← cyc3_inv_of_ne hxw hwy hxy]
    exact inv_mem h
  · have hwT : w ∈ T := (Finset.mem_union.1 hw).resolve_left hwS
    have hI' : 3 ≤ (T ∩ S).card := by rwa [Finset.inter_comm]
    have h := cyc3_mem_sup_aux hI' hyT hyS hxS hxT hwT (Ne.symm hwy) (Ne.symm hxw)
    rw [sup_comm, ← cyc3_rotate_of_ne hxy (Ne.symm hwy) hxw] at h
    exact h

theorem altSub_sup_altSub {S T : Finset α} (hI : 3 ≤ (S ∩ T).card) :
    altSub S ⊔ altSub T = altSub (S ∪ T) := by
  refine le_antisymm (sup_le (altSub_mono Finset.subset_union_left)
    (altSub_mono Finset.subset_union_right)) ?_
  refine altSub_le_of_cyc3 (fun x y z hx hy hz hxy hyz hxz => ?_)
  by_cases hS : x ∈ S ∧ y ∈ S ∧ z ∈ S
  · exact Subgroup.mem_sup_left (cyc3_mem_altSub hS.1 hS.2.1 hS.2.2 hxy hyz hxz)
  by_cases hT : x ∈ T ∧ y ∈ T ∧ z ∈ T
  · exact Subgroup.mem_sup_right (cyc3_mem_altSub hT.1 hT.2.1 hT.2.2 hxy hyz hxz)
  have hs : x ∉ T ∨ y ∉ T ∨ z ∉ T := by
    by_contra hcon
    push Not at hcon
    exact hT ⟨hcon.1, hcon.2.1, hcon.2.2⟩
  have ht : x ∉ S ∨ y ∉ S ∨ z ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hS ⟨hcon.1, hcon.2.1, hcon.2.2⟩
  have hxS : x ∉ T → x ∈ S := fun h => (Finset.mem_union.1 hx).resolve_right h
  have hyS : y ∉ T → y ∈ S := fun h => (Finset.mem_union.1 hy).resolve_right h
  have hzS : z ∉ T → z ∈ S := fun h => (Finset.mem_union.1 hz).resolve_right h
  have hxT : x ∉ S → x ∈ T := fun h => (Finset.mem_union.1 hx).resolve_left h
  have hyT : y ∉ S → y ∈ T := fun h => (Finset.mem_union.1 hy).resolve_left h
  have hzT : z ∉ S → z ∈ T := fun h => (Finset.mem_union.1 hz).resolve_left h
  rcases hs with a | a | a <;> rcases ht with b | b | b
  · exact absurd (hxS a) b
  · exact cyc3_mem_sup_mixed hI (hxS a) a (hyT b) b hz hxz (Ne.symm hyz)
  · have h := cyc3_mem_sup_mixed hI (hxS a) a (hzT b) b hy hxy hyz
    rw [← cyc3_inv_of_ne hxz hyz.symm hxy]
    exact inv_mem h
  · have h := cyc3_mem_sup_mixed hI (hyS a) a (hxT b) b hz hyz hxz.symm
    rw [cyc3_rotate_of_ne hxy hyz hxz, ← cyc3_inv_of_ne hxy.symm hxz hyz]
    exact inv_mem h
  · exact absurd (hyS a) b
  · have h := cyc3_mem_sup_mixed hI (hyS a) a (hzT b) b hx hxy.symm hxz
    rw [cyc3_rotate_of_ne hxy hyz hxz]
    exact h
  · have h := cyc3_mem_sup_mixed hI (hzS a) a (hxT b) b hy hyz.symm hxy.symm
    rw [cyc3_rotate_of_ne hxy hyz hxz, cyc3_rotate_of_ne hyz hxz.symm hxy.symm]
    exact h
  · have h := cyc3_mem_sup_mixed hI (hzS a) a (hyT b) b hx hxz.symm hxy
    have e1 := cyc3_inv_of_ne hyz.symm hxy.symm hxz.symm
    rw [cyc3_rotate_of_ne hxy hyz hxz, cyc3_rotate_of_ne hyz hxz.symm hxy.symm, ← e1]
    exact inv_mem h
  · exact absurd (hzS a) b

end Gen

end Alt

end CFSG.OddStandard.AltStdSec
