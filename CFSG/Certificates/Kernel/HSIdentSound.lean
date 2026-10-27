module

public import Certificates.Data.Kernel.HSIdent

public section

namespace CFSG.KC.HSIdent

open Certificates.Kernel.HSIdent CFSG.ComponentClassification.WittDesign
  CFSG.Monster.B.Classical.Plane CFSG.Sporadic.Recognition.HSGraph
  CFSG.Sporadic.Recognition.HSPinned CFSG.Sporadic.Recognition.HSPinned.Native

theorem allBelow_sound {p : Nat → Bool} :
    ∀ {n : Nat}, allBelow p n = true → ∀ i < n, p i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    rw [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact allBelow_sound h.1 i hi
    · exact h.2

theorem testBit_lmask : ∀ (l : List Nat) (b : Nat), (lmask l).testBit b = true ↔ b ∈ l
  | [], b => by simp [lmask]
  | t :: l, b => by
    rw [lmask, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, testBit_lmask l b,
      List.mem_cons, decide_eq_true_iff, eq_comm]

theorem any_contains_iff (l l' : List Nat) :
    (l.any fun t => l'.contains t) = true ↔ lmask l &&& lmask l' ≠ 0 := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, ht'⟩ h0
    have h1 := congrArg (fun m => m.testBit t) h0
    simp only [Nat.testBit_and, Nat.zero_testBit] at h1
    rw [(testBit_lmask l t).2 ht, (testBit_lmask l' t).2 (List.elem_iff.1 ht')] at h1
    exact Bool.noConfusion h1
  · intro h
    obtain ⟨t, ht⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_and, Bool.and_eq_true, testBit_lmask, testBit_lmask] at ht
    exact ⟨t, ht.1, List.elem_iff.2 ht.2⟩

theorem testBit_foldl (P : Nat → Bool) (b : Nat) :
    ∀ (l : List Nat) (m : Nat),
      (l.foldl (fun m y => if P y then m ||| 1 <<< y else m) m).testBit b = true ↔
        m.testBit b = true ∨ (b ∈ l ∧ P b = true)
  | [], m => by simp
  | y :: l, m => by
    rw [List.foldl_cons, testBit_foldl P b l]
    by_cases hy : P y = true
    · rw [if_pos hy, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hb : y = b
      · subst hb
        simp [hy]
      · simp [hb, Ne.symm hb]
    · rw [if_neg hy]
      by_cases hb : y = b
      · subst hb
        simp [hy]
      · simp only [List.mem_cons, Ne.symm hb, false_or]

theorem adjB_eq {x y : Nat} (hx : x < 100) (hy : y < 100) :
    adjB x y = (x != y && decide (lmask stars[x]! &&& lmask stars[y]! ≠ 0)) := by
  have hrow : (adjRows ())[x]! = (List.range 100).foldl
      (fun m y => if (x != y && (stars[x]!).any (fun t => (stars[y]!).contains t)) = true then
        m ||| (1 <<< y) else m) 0 := by
    rw [adjRows, getElem!_pos _ _ (by simpa using hx), Array.getElem_map, Array.getElem_range]
  rw [adjB, hrow]
  apply Bool.eq_iff_iff.2
  rw [testBit_foldl _ y, Bool.and_eq_true, Bool.and_eq_true, any_contains_iff,
    decide_eq_true_iff, List.mem_range]
  simp [hy]

theorem testBit_mask_iff {n : Nat} (A : Finset (Fin n)) (i : Nat) :
    (mask A).testBit i = true ↔ ∃ a ∈ A, (a : Nat) = i := by
  have h := Finset.toFinset_bitIndices_sum_two_pow (A.map Fin.valEmbedding)
  rw [Finset.sum_map] at h
  have h2 := congrArg (i ∈ ·) h
  simp only [List.mem_toFinset, Nat.mem_bitIndices, Finset.mem_map, Fin.valEmbedding_apply,
    eq_iff_iff] at h2
  exact h2

theorem disjoint_iff_mask {n : Nat} (A B : Finset (Fin n)) :
    Disjoint A B ↔ mask A &&& mask B = 0 := by
  rw [Finset.disjoint_left]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_iff]
    by_contra hc
    simp only [not_or, Bool.not_eq_false] at hc
    obtain ⟨a, ha, rfl⟩ := (testBit_mask_iff A i).1 hc.1
    obtain ⟨b, hb, hab⟩ := (testBit_mask_iff B _).1 hc.2
    exact h ha (Fin.ext hab ▸ hb)
  · intro h a ha hb
    have h1 := congrArg (fun m => m.testBit a) h
    simp only [Nat.testBit_and, Nat.zero_testBit] at h1
    rw [(testBit_mask A a).2 ha, (testBit_mask B a).2 hb] at h1
    exact Bool.noConfusion h1

theorem vert_cases {n : Nat} (hn : n < 100) :
    n = 0 ∨ (∃ k, k < 22 ∧ n = k + 1) ∨ (∃ k, k < 77 ∧ n = k + 23) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inl h
  · by_cases h22 : n ≤ 22
    · exact Or.inr (Or.inl ⟨n - 1, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨n - 23, by omega, by omega⟩)

theorem modelVertAt_zero : modelVertAt 0 = vInf := by
  rw [modelVertAt, if_pos rfl]

theorem modelVertAt_pt {k : Nat} (hk : k < 22) : modelVertAt (k + 1) = vPt ⟨k, hk⟩ := by
  rw [modelVertAt, if_neg (by omega), if_pos (by omega)]
  exact congrArg (fun a : Fin 22 => (vPt a : Vert hexads))
    (Fin.ext (by change (k + 1 - 1) % 22 = k; omega))

theorem modelVertAt_blk (k : Nat) : modelVertAt (k + 23) = vBlk (modelBlkAt k) := by
  rw [modelVertAt, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]

theorem modelAdjN_zero (m : Nat) : modelAdjN 0 m = (decide (1 ≤ m) && decide (m ≤ 22)) := by
  rw [modelAdjN, if_pos rfl]

theorem modelAdjN_pt {k : Nat} (hk : k < 22) (m : Nat) : modelAdjN (k + 1) m =
    (decide (m = 0) || (decide (23 ≤ m) && (hexMask (m - 23)).testBit k)) := by
  rw [modelAdjN, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel]

theorem modelAdjN_blk (k m : Nat) : modelAdjN (k + 23) m =
    ((decide (1 ≤ m) && decide (m ≤ 22) && (hexMask k).testBit (m - 1)) ||
      (decide (23 ≤ m) && decide (hexMask k ≠ hexMask (m - 23)) &&
        decide (hexMask k &&& hexMask (m - 23) = 0))) := by
  rw [modelAdjN, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]

theorem testBit_hexMask (l k : Nat) (hk : k < 22) :
    (hexMask l).testBit k = true ↔ (⟨k, hk⟩ : Fin 22) ∈ (modelBlkAt l).1 :=
  testBit_mask _ ⟨k, hk⟩

theorem hexMask_adj (k l : Nat) :
    (decide (hexMask k ≠ hexMask l) && decide (hexMask k &&& hexMask l = 0)) = true ↔
      modelBlkAt k ≠ modelBlkAt l ∧ Disjoint (modelBlkAt k).1 (modelBlkAt l).1 := by
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, hexMask, hexMask,
    ← disjoint_iff_mask, ne_eq, ne_eq, Subtype.ext_iff]
  exact and_congr_left' (not_congr ⟨fun h => mask_injective h, congrArg mask⟩)

theorem modelAdjN_iff {n m : Nat} (hn : n < 100) (hm : m < 100) :
    modelAdjN n m = true ↔ (hsGraph hexads).Adj (modelVertAt n) (modelVertAt m) := by
  rcases vert_cases hn with rfl | ⟨k, hk, rfl⟩ | ⟨k, -, rfl⟩ <;>
    rcases vert_cases hm with rfl | ⟨l, hl, rfl⟩ | ⟨l, -, rfl⟩
  · rw [modelAdjN_zero, modelVertAt_zero]
    simp
  · rw [modelAdjN_zero, modelVertAt_zero, modelVertAt_pt hl]
    simp only [adj_vInf_vPt, iff_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · rw [modelAdjN_zero, modelVertAt_zero, modelVertAt_blk]
    simp only [not_adj_vInf_vBlk, iff_false, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · rw [modelAdjN_pt hk, modelVertAt_pt hk, modelVertAt_zero]
    simp
  · rw [modelAdjN_pt hk, modelVertAt_pt hk, modelVertAt_pt hl]
    simp only [not_adj_vPt_vPt, iff_false, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    rintro (h | ⟨h, _⟩) <;> omega
  · rw [modelAdjN_pt hk, modelVertAt_pt hk, modelVertAt_blk, adj_vPt_vBlk,
      ← testBit_hexMask l k hk]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Nat.add_sub_cancel]
    constructor
    · rintro (h | ⟨_, h⟩)
      · omega
      · exact h
    · intro h
      exact Or.inr ⟨by omega, h⟩
  · rw [modelAdjN_blk, modelVertAt_blk, modelVertAt_zero]
    simp
  · rw [modelAdjN_blk, modelVertAt_blk, modelVertAt_pt hl, adj_vBlk_vPt,
      ← testBit_hexMask k l hl]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Nat.add_sub_cancel]
    constructor
    · rintro (⟨_, h⟩ | ⟨⟨h, _⟩, _⟩)
      · exact h
      · omega
    · intro h
      exact Or.inl ⟨⟨by omega, by omega⟩, h⟩
  · rw [modelAdjN_blk, modelVertAt_blk, modelVertAt_blk, adj_vBlk_vBlk, ← hexMask_adj,
      Nat.add_sub_cancel]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨⟨_, h⟩, _⟩ | ⟨⟨_, h1⟩, h2⟩)
      · omega
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨⟨by omega, h1⟩, h2⟩

theorem iso_check_of (h : identCheckOn isoList stars = true) :
    ∀ i j : Fin 100, adjB i.val j.val = true ↔
      (hsGraph hexads).Adj (modelVertAtF (isoFun i)) (modelVertAtF (isoFun j)) := by
  intro i j
  have hij := allBelow_sound (allBelow_sound h i.val i.isLt) j.val j.isLt
  rw [beq_iff_eq] at hij
  rw [adjB_eq i.isLt j.isLt, hij]
  exact modelAdjN_iff (isoFun i).isLt (isoFun j).isLt

theorem isoFun_injective_of (h : injCheckOn isoList = true) :
    ∀ i j : Fin 100, isoFun i = isoFun j → i = j := by
  intro i j hij
  have h1 := allBelow_sound (allBelow_sound h i.val i.isLt) j.val j.isLt
  rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h1
  rcases h1 with h1 | h1
  · exact Fin.ext h1
  · exact absurd (congrArg Fin.val hij) h1

end CFSG.KC.HSIdent
