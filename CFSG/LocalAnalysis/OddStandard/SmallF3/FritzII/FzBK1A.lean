module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBI2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzBU

private theorem xor_lt_four {a b : ℕ} (ha : a < 4) (hb : b < 4) : a ^^^ b < 4 := by
  have h := Nat.xor_lt_two_pow (n := 2) (x := a) (y := b)
    (by change a < 4; exact ha) (by change b < 4; exact hb)
  change a ^^^ b < 4 at h
  exact h

private theorem f4mul_lt (a b : ℕ) : f4mul a b < 4 := by
  unfold f4mul
  have h1 : (a % 2 * (b % 2) + a / 2 * (b / 2)) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h2 : (a % 2 * (b / 2) + a / 2 * (b % 2) + a / 2 * (b / 2)) % 2 < 2 :=
    Nat.mod_lt _ (by norm_num)
  omega

private theorem range_map_getElem! (f : ℕ → ℕ) {n i : ℕ} (hi : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  have hsize : i < ((Array.range n).map f).size := by
    simpa [Array.size_map, Array.size_range] using hi
  rw [getElem!_pos ((Array.range n).map f) i hsize, Array.getElem_map, Array.getElem_range]

private theorem mulA_congr {M N : Mod} (h1 : M.aq = N.aq) (h2 : M.as = N.as) (h3 : M.ay = N.ay) :
    M.mulA = N.mulA := by
  funext x y
  simp only [Mod.mulA, Mod.act, h1, h2, h3]

private def modl0 (c : Bool) : Mod :=
  let r := (repImgs c).map (extArr (wordTab ()))
  ⟨r[0]!, r[1]!, r[2]!, #[]⟩

private theorem modl_tab (c : Bool) :
    (modl c ()).tab = (Array.range 1048576).map
      (fun i => (modl c ()).mulA (i / 1024) (i % 1024)) := by
  rw [mulA_congr (M := modl c ()) (N := modl0 c) rfl rfl rfl]
  rfl

theorem fzb_allBelow_iff (p : ℕ → Bool) (n : ℕ) :
    allBelow p n = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem fzb_anyBelow_iff (p : ℕ → Bool) (n : ℕ) :
    anyBelow p n = true ↔ ∃ i < n, p i = true := by
  induction n with
  | zero => simp [anyBelow]
  | succ n ih =>
    simp only [anyBelow, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, hpi⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, hpi⟩
    · rintro ⟨i, hi, hpi⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inr ⟨i, hi, hpi⟩
      · exact Or.inl hpi

theorem fzb_countBelow_eq (p : ℕ → Bool) (n : ℕ) :
    countBelow p n = ((Finset.range n).filter (fun i => p i = true)).card := by
  induction n with
  | zero => simp [countBelow]
  | succ n ih =>
    rw [countBelow, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : p n = true
    · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
      omega
    · rw [if_neg h, if_neg h]
      omega

theorem fzb_uMul_lt {x y : ℕ} (hx : x < 64) (hy : y < 64) : uMul x y < 64 := by
  unfold uMul
  have hx16 : x / 16 < 4 := by omega
  have hy16 : y / 16 < 4 := by omega
  have hx4 : x / 4 % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hy4 : y / 4 % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hxr : x % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hyr : y % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hA : (x / 16) ^^^ (y / 16) < 4 := xor_lt_four hx16 hy16
  have hB : (x / 4 % 4) ^^^ (y / 4 % 4) < 4 := xor_lt_four hx4 hy4
  have hC : ((x % 4) ^^^ (y % 4)) ^^^ f4mul (x / 16) (y / 4 % 4) < 4 :=
    xor_lt_four (xor_lt_four hxr hyr) (f4mul_lt _ _)
  omega

theorem fzb_amul_lt (w w' : ℕ) : amul w w' < 16 := by
  unfold amul
  have h1 : (w % 4 + (if w / 4 % 2 == 0 then w' % 4 else (4 - w' % 4) % 4)) % 4 < 4 :=
    Nat.mod_lt _ (by norm_num)
  have h2 : (w / 4 % 2 + w' / 4 % 2) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h3 : (w / 8 + w' / 8) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  omega

theorem fzb_mul_eq_mulA (c : Bool) (x y : ℕ) :
    fzbMul c x y = (modl c ()).mulA x y := by
  unfold fzbMul Certificates.FzBU.Mod.mul
  by_cases hxy : x < 1024 ∧ y < 1024
  · rw [if_pos hxy]
    obtain ⟨hx, hy⟩ := hxy
    rw [modl_tab c]
    rw [range_map_getElem! (fun i => (modl c ()).mulA (i / 1024) (i % 1024))
      (show x * 1024 + y < 1048576 by omega)]
    rw [Nat.mul_comm x 1024, Nat.mul_add_div (by norm_num : 0 < 1024) x y,
      Nat.div_eq_of_lt hy, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]
  · rw [if_neg hxy]

end CFSG.OddStandard.SmallF3.FritzII
