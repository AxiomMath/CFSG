module

import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.A7Index15
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.AGLEmbeddingD2.GN

open Equiv Equiv.Perm

section Explicit

def a7SylR : Perm (Fin 7) := swap 1 2 * swap 2 3 * swap 3 4 * swap 5 6

def a7SylS : Perm (Fin 7) := swap 1 3 * swap 5 6

def a7SylList : List (Perm (Fin 7)) :=
  [1, a7SylR, swap 1 3 * swap 2 4, swap 5 6 * swap 3 4 * swap 2 3 * swap 1 2, a7SylS,
    swap 1 2 * swap 3 4, swap 2 4 * swap 5 6, swap 1 4 * swap 2 3]

theorem a7_syl_check :
    (a7SylList.all fun a => a7SylList.all fun b => a7SylList.contains (a * b)) &&
    a7SylList.all (fun a => decide (sign a = 1)) &&
    a7SylList.all (fun a => decide (a * a * a * a = 1)) &&
    a7SylList.all (fun a => decide (a 0 = 0)) &&
    decide a7SylList.Nodup = true := by
  decide +kernel

theorem a7_syl_mul {a b : Perm (Fin 7)} (ha : a ∈ a7SylList) (hb : b ∈ a7SylList) :
    a * b ∈ a7SylList := by
  have h := a7_syl_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h.1.1.1.1 a ha b hb

theorem a7_syl_sign {a : Perm (Fin 7)} (ha : a ∈ a7SylList) : sign a = 1 := by
  have h := a7_syl_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2 a ha

theorem a7_syl_pow {a : Perm (Fin 7)} (ha : a ∈ a7SylList) : a * a * a * a = 1 := by
  have h := a7_syl_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2 a ha

theorem a7_syl_fix {a : Perm (Fin 7)} (ha : a ∈ a7SylList) : a 0 = 0 := by
  have h := a7_syl_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.2 a ha

theorem a7_syl_nodup : a7SylList.Nodup := by
  have h := a7_syl_check
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem a7_syl_fix_check : ((List.finRange 7).all fun x =>
    !(a7SylList.all fun a => decide (a x = x)) || decide (x = 0)) = true := by
  decide +kernel

theorem a7_syl_fix_unique : ∀ x : Fin 7, (∀ a ∈ a7SylList, a x = x) → x = 0 := by
  intro x hx
  have h := a7_syl_fix_check
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  have := h x (List.mem_finRange x)
  rcases this with h1 | h1
  · exfalso
    rw [List.all_eq_false] at h1
    obtain ⟨a, ha, hne⟩ := h1
    exact (by simpa using hne : ¬ a x = x) (hx a ha)
  · exact h1

set_option maxRecDepth 100000 in
theorem a7_syl_normalizer : ∀ g : Perm (Fin 7), g 0 = 0 → g * a7SylR * g⁻¹ ∈ a7SylList →
    g * a7SylS * g⁻¹ ∈ a7SylList → sign g = 1 → g ∈ a7SylList := by
  decide +kernel

theorem a7SylR_mem : a7SylR ∈ a7SylList := by simp [a7SylList]

theorem a7SylS_mem : a7SylS ∈ a7SylList := by simp [a7SylList]

def a7SylSub : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {g | (g : Perm (Fin 7)) ∈ a7SylList}
  mul_mem' ha hb := a7_syl_mul ha hb
  one_mem' := List.mem_cons_self
  inv_mem' {a} ha := by
    have hinv : (a : Perm (Fin 7))⁻¹ = a * a * a :=
      inv_eq_of_mul_eq_one_right (by simpa only [mul_assoc] using a7_syl_pow ha)
    change (a : Perm (Fin 7))⁻¹ ∈ a7SylList
    rw [hinv]
    exact a7_syl_mul (a7_syl_mul ha ha) ha

theorem isPGroup_a7SylSub : IsPGroup 2 a7SylSub := fun g => ⟨2, by
  have h4 := a7_syl_pow g.2
  refine Subtype.ext (Subtype.ext ?_)
  simpa [pow_succ, mul_assoc] using h4⟩

theorem card_a7SylSub : Nat.card a7SylSub = 8 := by
  have h1 : Nat.card a7SylSub = Nat.card {σ : Perm (Fin 7) // σ ∈ a7SylList} := by
    refine Nat.card_congr ⟨fun g => ⟨g.1.1, g.2⟩, fun σ => ⟨⟨σ.1, mem_alternatingGroup.2
      (a7_syl_sign σ.2)⟩, σ.2⟩, fun g => rfl, fun σ => rfl⟩
  rw [h1, Nat.card_eq_fintype_card]
  have h2 : Fintype.card {σ : Perm (Fin 7) // σ ∈ a7SylList} = a7SylList.toFinset.card := by
    rw [← Fintype.card_coe a7SylList.toFinset]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => by simp)
  rw [h2, List.toFinset_card_of_nodup a7_syl_nodup]
  rfl

theorem not_two_dvd_index_a7SylSub : ¬ 2 ∣ a7SylSub.index := by
  have h := a7SylSub.card_mul_index
  rw [card_a7SylSub,
    CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.card_alternatingGroup_seven] at h
  omega

theorem mem_a7SylSub_of_normalizes {g : alternatingGroup (Fin 7)}
    (h1 : ∀ h ∈ a7SylSub, g * h * g⁻¹ ∈ a7SylSub) (h2 : ∀ h ∈ a7SylSub, g⁻¹ * h * g ∈ a7SylSub) :
    g ∈ a7SylSub := by
  have hr : g * (⟨a7SylR, mem_alternatingGroup.2 (a7_syl_sign a7SylR_mem)⟩ :
      alternatingGroup (Fin 7)) * g⁻¹ ∈ a7SylSub := h1 _ a7SylR_mem
  have hs : g * (⟨a7SylS, mem_alternatingGroup.2 (a7_syl_sign a7SylS_mem)⟩ :
      alternatingGroup (Fin 7)) * g⁻¹ ∈ a7SylSub := h1 _ a7SylS_mem
  have h0 : (g : Perm (Fin 7)) 0 = 0 := by
    apply a7_syl_fix_unique
    intro a ha
    have hmem : (⟨a, mem_alternatingGroup.2 (a7_syl_sign ha)⟩ : alternatingGroup (Fin 7)) ∈
        a7SylSub := ha
    have h3 : (g : Perm (Fin 7))⁻¹ * a * (g : Perm (Fin 7)) ∈ a7SylList := h2 _ hmem
    have h5 : (g : Perm (Fin 7))⁻¹ (a ((g : Perm (Fin 7)) 0)) = 0 := a7_syl_fix h3
    exact Equiv.Perm.inv_eq_iff_eq.1 h5
  exact a7_syl_normalizer g h0 hr hs (mem_alternatingGroup.1 g.2)

end Explicit

end CFSG.AGLEmbeddingD2.GN
