module

public import CFSG.Certificates.CosetTablePresented
public import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.KC.MiscCoset

open CFSG.CosetTable

theorem relIndex_le_of_central {G : Type*} [Group G] {H K : Subgroup G} (z : G) (n : ℕ)
    (hzK : z ∈ K) (hK : ∀ k ∈ K, ∃ j < n, ∃ h ∈ H, k = z ^ j * h) :
    H.relIndex K ≠ 0 ∧ H.relIndex K ≤ n := by
  rw [Subgroup.relIndex, Subgroup.index]
  let f : Fin n → K ⧸ H.subgroupOf K := fun j => QuotientGroup.mk ⟨z ^ j.val, K.pow_mem hzK _⟩
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨j, hj, h, hh, he⟩ := hK k k.2
      refine ⟨⟨j, hj⟩, QuotientGroup.eq.2 ?_⟩
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, he, inv_mul_cancel_left]
      exact hh
  have : Finite (K ⧸ H.subgroupOf K) := Finite.of_surjective f hf
  refine ⟨Nat.card_pos.ne', ?_⟩
  have := Nat.card_le_card_of_surjective f hf
  simpa using this

theorem genSub_central_form {m : ℕ} {rels : Set (FreeGroup (Fin m))} {S T : List (Fin m)} {a : Fin m}
    {n : ℕ} (hn : 1 < n) (hz : ∀ g : PresentedGroup rels, PresentedGroup.of a * g = g * PresentedGroup.of a)
    (hzn : PresentedGroup.of a ^ n ∈ genSub rels S) (hT : ∀ x ∈ T, x = a ∨ x ∈ S) :
    ∀ k ∈ genSub rels T, ∃ j < n, ∃ h ∈ genSub rels S, k = PresentedGroup.of a ^ j * h := by
  set z : PresentedGroup rels := PresentedGroup.of a
  set H := genSub rels S
  have hc : ∀ (j : ℕ) (g : PresentedGroup rels), z ^ j * g = g * z ^ j :=
    fun j g => ((Commute.pow_left (hz g) j)).eq
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem k hk =>
    obtain ⟨x, hx, rfl⟩ := hk
    rcases hT x hx with rfl | hS
    · exact ⟨1, by omega, 1, H.one_mem, by rw [pow_one, mul_one]⟩
    · exact ⟨0, by omega, _, Subgroup.subset_closure ⟨x, hS, rfl⟩, by rw [pow_zero, one_mul]⟩
  | one => exact ⟨0, by omega, 1, H.one_mem, by rw [pow_zero, one_mul]⟩
  | mul k1 k2 _ _ ih1 ih2 =>
    obtain ⟨a1, ha1, h1, hh1, rfl⟩ := ih1
    obtain ⟨a2, ha2, h2, hh2, rfl⟩ := ih2
    have e : z ^ a1 * h1 * (z ^ a2 * h2) = z ^ (a1 + a2) * (h1 * h2) := by
      rw [pow_add, mul_assoc, ← mul_assoc h1, ← hc a2 h1, mul_assoc, mul_assoc]
    rw [e]
    by_cases hlt : a1 + a2 < n
    · exact ⟨a1 + a2, hlt, _, H.mul_mem hh1 hh2, rfl⟩
    · refine ⟨a1 + a2 - n, by omega, z ^ n * (h1 * h2), H.mul_mem hzn (H.mul_mem hh1 hh2), ?_⟩
      rw [← mul_assoc (z ^ (a1 + a2 - n)), ← pow_add, Nat.sub_add_cancel (by omega : n ≤ a1 + a2)]
  | inv k _ ih =>
    obtain ⟨a1, ha1, h1, hh1, rfl⟩ := ih
    rcases Nat.eq_zero_or_pos a1 with h0 | hpos
    · refine ⟨0, by omega, h1⁻¹, H.inv_mem hh1, ?_⟩
      rw [h0, pow_zero, one_mul, one_mul]
    · refine ⟨n - a1, by omega, h1⁻¹ * (z ^ n)⁻¹, H.mul_mem (H.inv_mem hh1) (H.inv_mem hzn), ?_⟩
      have hp : z ^ n = z ^ a1 * z ^ (n - a1) := by rw [← pow_add, Nat.add_sub_cancel' ha1.le]
      rw [mul_inv_rev, hp, mul_inv_rev, ← mul_assoc, hc (n - a1) h1⁻¹, mul_assoc,
        mul_inv_cancel_left]

theorem genSub_index_le_central {m : ℕ} {rels : Set (FreeGroup (Fin m))} {S T : List (Fin m)}
    {a : Fin m} {n N : ℕ} (hn : 1 < n)
    (hz : ∀ g : PresentedGroup rels, PresentedGroup.of a * g = g * PresentedGroup.of a)
    (hzn : PresentedGroup.of a ^ n ∈ genSub rels S) (hT : ∀ x ∈ T, x = a ∨ x ∈ S)
    (hST : ∀ x ∈ S, x ∈ T) (haT : a ∈ T)
    (h : (genSub rels T).FiniteIndex ∧ (genSub rels T).index ≤ N) :
    (genSub rels S).FiniteIndex ∧ (genSub rels S).index ≤ n * N := by
  have hHK : genSub rels S ≤ genSub rels T :=
    Subgroup.closure_mono (Set.image_mono fun x hx => hST x hx)
  have hzK : PresentedGroup.of a ∈ genSub rels T := Subgroup.subset_closure ⟨a, haT, rfl⟩
  have hrel := relIndex_le_of_central _ n hzK (genSub_central_form hn hz hzn hT)
  have hmul := Subgroup.relIndex_mul_index hHK
  have hK0 : (genSub rels T).index ≠ 0 := h.1.index_ne_zero
  refine ⟨⟨by rw [← hmul]; exact mul_ne_zero hrel.1 hK0⟩, ?_⟩
  rw [← hmul]
  exact Nat.mul_le_mul hrel.2 h.2

end CFSG.KC.MiscCoset
