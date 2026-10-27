module

public import Certificates.Data.Kernel.U4FFLocCheck
public import CFSG.Certificates.Kernel.U4FFLocSound

public section

namespace CFSG.KC.U4FFLoc

open CFSG.HardMathSupport.U4FF

theorem packL_lane (P c j : ℕ) (hc : c < 2 ^ 128) :
    (2 ^ 128 * P + c).testBit j = if j < 128 then c.testBit j else P.testBit (j - 128) :=
  Nat.testBit_two_pow_mul_add P hc j

theorem unpackL_packL : ∀ C : List ℕ, (∀ c ∈ C, c < 2 ^ 128) → unpackL C.length (packL C) = C
  | [], _ => rfl
  | c :: C, h => by
    have hc : c < 2 ^ 128 := h c List.mem_cons_self
    have ih := unpackL_packL C (fun d hd => h d (List.mem_cons_of_mem _ hd))
    simp only [List.length_cons, unpackL, packL]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc, Nat.mul_add_div (Nat.two_pow_pos 128),
      Nat.div_eq_of_lt hc, Nat.add_zero, ih]

theorem packL_map_zero (x : List ℕ) : packL (x.map fun _ => 0) = 0 := by
  induction x with
  | nil => rfl
  | cons c x ih => simp only [List.map_cons, packL, ih, Nat.mul_zero, Nat.add_zero]

theorem mul_packL (a : ℕ) (s : List ℕ) : a * packL s = packL (s.map (a * ·)) := by
  induction s with
  | nil => simp [packL]
  | cons c s ih =>
    simp only [packL, List.map_cons]
    rw [← ih]
    ring

theorem lane_xor (P Q c d : ℕ) (hc : c < 2 ^ 128) (hd : d < 2 ^ 128) :
    (2 ^ 128 * P + c) ^^^ (2 ^ 128 * Q + d) = 2 ^ 128 * (P ^^^ Q) + (c ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, packL_lane _ _ _ hc, packL_lane _ _ _ hd,
    packL_lane _ _ _ (Nat.xor_lt_two_pow hc hd)]
  split_ifs <;> simp [Nat.testBit_xor]

theorem packL_xor (f g : ℕ → ℕ) : ∀ x : List ℕ, (∀ c ∈ x, f c < 2 ^ 128) →
    (∀ c ∈ x, g c < 2 ^ 128) →
      packL (x.map f) ^^^ packL (x.map g) = packL (x.map fun c => f c ^^^ g c)
  | [], _, _ => by simp only [List.map_nil, packL, Nat.zero_xor]
  | c :: x, hf, hg => by
    simp only [List.map_cons, packL]
    rw [lane_xor _ _ _ _ (hf c List.mem_cons_self) (hg c List.mem_cons_self),
      packL_xor f g x (fun d hd => hf d (List.mem_cons_of_mem _ hd))
        (fun d hd => hg d (List.mem_cons_of_mem _ hd))]

theorem shift_and_ones (t : ℕ) (ht : t < 128) : ∀ x : List ℕ, (∀ c ∈ x, c < 2 ^ 128) →
    (packL x >>> t) &&& packL (List.replicate x.length 1) =
      packL (x.map fun c => (c >>> t) % 2)
  | [], _ => by simp [packL]
  | c :: x, h => by
    have hc : c < 2 ^ 128 := h c List.mem_cons_self
    have ih := shift_and_ones t ht x (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have h1 : (1 : ℕ) < 2 ^ 128 := Nat.one_lt_two_pow (by norm_num)
    have h2 : (c >>> t) % 2 < 2 ^ 128 :=
      lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [List.length_cons, List.replicate_succ, List.map_cons, packL]
    rw [Nat.testBit_and, Nat.testBit_shiftRight, packL_lane _ _ _ hc, packL_lane _ _ _ h1,
      packL_lane _ _ _ h2]
    by_cases hj : j < 128
    · rw [if_pos hj, if_pos hj]
      rcases j with _ | j
      · have e : c.testBit t = (c >>> t).testBit 0 := by
          rw [Nat.testBit_shiftRight, Nat.add_zero]
        rw [if_pos (by omega), Nat.add_zero, e, Nat.testBit_one_zero, Bool.and_true,
          Nat.testBit_zero, Nat.testBit_zero, Nat.mod_mod]
      · have e1 : (1 : ℕ).testBit (j + 1) = false :=
          Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
        have e2 : ((c >>> t) % 2).testBit (j + 1) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
            (Nat.le_self_pow (by omega) 2))
        rw [e1, e2, Bool.and_false]
    · rw [if_neg hj, if_neg hj, if_neg (by omega), ← ih, Nat.testBit_and, Nat.testBit_shiftRight]
      have e : t + j - 128 = t + (j - 128) := by omega
      rw [e]

theorem applyL_lt : ∀ (A : List ℕ) (v : ℕ), (∀ a ∈ A, a < 2 ^ 128) → applyL A v < 2 ^ 128
  | [], _, _ => by simp [applyL]
  | a :: A, v, h => by
    rw [applyL]
    apply Nat.xor_lt_two_pow
    · split_ifs
      · exact h a List.mem_cons_self
      · exact Nat.two_pow_pos _
    · exact applyL_lt A _ (fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem mulPgo_eq (x : List ℕ) (hx : ∀ c ∈ x, c < 2 ^ 128) :
    ∀ (A : List ℕ) (t : ℕ), (∀ a ∈ A, a < 2 ^ 128) → t + A.length ≤ 128 →
      mulPgo (packL x) (packL (List.replicate x.length 1)) A t =
        packL (x.map fun c => applyL A (c >>> t))
  | [], t, _, _ => by
    simp only [mulPgo, applyL]
    exact (packL_map_zero x).symm
  | a :: A, t, hA, ht => by
    have ha := hA a List.mem_cons_self
    have hA' : ∀ b ∈ A, b < 2 ^ 128 := fun b hb => hA b (List.mem_cons_of_mem _ hb)
    simp only [List.length_cons] at ht
    rw [mulPgo, shift_and_ones t (by omega) x hx, mul_packL,
      mulPgo_eq x hx A (t + 1) hA' (by omega), List.map_map, packL_xor]
    · congr 1
      apply List.map_congr_left
      intro c _
      simp only [Function.comp, applyL, Nat.shiftRight_succ]
      rcases Nat.mod_two_eq_zero_or_one (c >>> t) with h | h <;> simp [h]
    · intro c _
      rcases Nat.mod_two_eq_zero_or_one (c >>> t) with h | h
      · simp [Function.comp, h, Nat.two_pow_pos]
      · simpa [Function.comp, h] using ha
    · intro c _
      exact applyL_lt A _ hA'

theorem mulPL_eq (A B : List ℕ) : mulPL A B = mulL A B := by
  unfold mulPL
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨hlen, hA⟩, hB⟩ := h
    rw [mulPgo_eq B hB A 0 hA (by omega)]
    have e := unpackL_packL (B.map fun c => applyL A (c >>> 0)) (by
      intro c hc
      obtain ⟨d, -, rfl⟩ := List.mem_map.mp hc
      exact applyL_lt A _ hA)
    rw [List.length_map] at e
    rw [e]
    simp [mulL]
  · rfl

theorem mcols_eq_iff (A B : MCols) : A = B ↔ A.toList = B.toList := Array.toList_inj.symm

theorem size_eq_length (A : MCols) : A.size = A.toList.length := Array.length_toList.symm

theorem hwEnc_eq (fs : List FK) : hwEnc fs = hwEncK fs := by
  induction fs with
  | nil =>
    have h := (ambEq [] (hwIdx [])).isLt
    simp only [ambDim, List.length_nil, Finset.univ_eq_empty, Finset.prod_empty] at h
    simp only [hwEnc, hwEncK]
    omega
  | cons K fs ih =>
    rw [hwEnc, ambEq_cons, hwEncK, ← ih]
    rfl

theorem toList_tabD (fs : List FK) (i j : Fin 4) (r : ℕ) :
    (tabD fs i j r).toList = tabDK fs i j r := (tabDK_eq_tabD fs i j r).symm

theorem toList_piOf (n : ℕ) (D : LocData) : (piOf n D).toList = piL n D := by
  simp only [piOf, piL, mulPL_eq, toList_add, toList_mul, toList_col, toList_zrowOf]

theorem yMasks_eq (fs : List FK) (D : LocData) : yMasks fs D = yL fs D := by
  rw [yMasks, yL, apply_eq, hwEnc_eq]

theorem toList_elemMasks (fs : List FK) (i j : Fin 4) :
    (elemMasks fs i j).toList = elemL fs i j := by
  unfold elemMasks elemL
  have key : ∀ (l : List ℕ) (acc : MCols),
      (l.foldl (fun acc r => MCols.add acc (tabD fs i j r)) acc).toList =
        l.foldl (fun acc r => addL acc (tabDK fs i j r)) acc.toList := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons r l ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih, toList_add, toList_tabD]
  rw [key, toList_zero, dimL_eq]

theorem toList_a1Masks (fs : List FK) : (a1Masks fs).toList = a1L fs := by
  simp only [a1Masks, a1L, toList_add, toList_elemMasks, toList_one, dimL_eq]

theorem toList_a2Masks (fs : List FK) : (a2Masks fs).toList = a2L fs := by
  simp only [a2Masks, a2L, mulPL_eq, toList_add, toList_mul, toList_elemMasks, toList_one, dimL_eq]

theorem toList_locOpMasks (D : LocData) (A : MCols) :
    (locOpMasks D A).toList = locOpL D A.toList := by
  simp only [locOpMasks, locOpL, mulPL_eq, toList_mul]

theorem toList_dlocMasks (fs : List FK) (D : LocData) (i j : Fin 4) (r : ℕ) :
    (dlocMasks fs D i j r).toList = dlocL fs D i j r := by
  simp only [dlocMasks, dlocL, mulPL_eq, toList_mul, toList_tabD]

theorem locValid1_iff (a b c : Bool) : LocValid1 a b c ↔ LocValid1K a b c = true := by
  simp only [LocValid1, LocValid1K, loc1K, mulPL_eq, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.any_eq_true, List.mem_range, Finset.mem_range, all44,
    List.mem_finRange, true_implies, forall_const, mcols_eq_iff, size_eq_length, toList_mul,
    toList_one, toList_zero, toList_zrowOf, toList_piOf, apply_eq, toList_tabD, yMasks_eq,
    hwEnc_eq, dimL_eq, and_assoc]

theorem locValid2_iff (a b c : Bool) : LocValid2 a b c ↔ LocValid2K a b c = true := by
  simp only [LocValid2, LocValid2K, loc2K, RankOK, rankOKK, mulPL_eq, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, mcols_eq_iff, size_eq_length, toList_mul, toList_one, toList_locOpMasks,
    toList_a1Masks, toList_a2Masks, and_assoc]

theorem locValid3_iff (a b c : Bool) : LocValid3 a b c ↔ LocValid3K a b c = true := by
  simp only [LocValid3, LocValid3K, loc3K, mulPL_eq, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range, Finset.mem_range, all44, List.mem_finRange, true_implies,
    forall_const, mcols_eq_iff, size_eq_length, toList_mul, toList_one, apply_eq,
    toList_dlocMasks, yMasks_eq, and_assoc]

theorem locValid_iff (a b c : Bool) : LocValid a b c ↔ LocValidK a b c = true := by
  simp only [LocValid, LocValidK, Bool.and_eq_true, locValid1_iff, locValid2_iff, locValid3_iff,
    and_assoc]

end CFSG.KC.U4FFLoc
