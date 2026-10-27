module

import CFSG.Certificates.Kernel.U6LinProved
public import CFSG.Certificates.Kernel.U6LinSound
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2FlagData
public import Certificates.Data.Kernel.U6.FlagK

public section

namespace CFSG.KC.U6F2

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (bxor testBit_bitsOf xorFold xorFold_succ)
open CFSG.EvenSmallLie.UnitarySix.YamadaN2 (msum2 blk2Bits emb2Bits par640)

private theorem strictB_eqF (y : ℕ) (k : ℕ → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

private theorem blt_falseF {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · exact absurd (by simpa using e) h

private theorem pw2_eqF(w : ℕ) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

private theorem bit_eqF (X i : ℕ) : bit X i = X.testBit i := by
  have e : bit X i = Nat.beq ((X >>> i) % 2) 1 := by
    change Nat.beq ((X >>> i) &&& 1) 1 = _
    rw [Nat.and_one_is_mod]
  have h2 : X.testBit i = decide ((X >>> i) % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
  rw [e, h2]
  rcases Nat.mod_two_eq_zero_or_one (X >>> i) with h | h <;> rw [h] <;> rfl

private theorem testBit_nIfF (c : Bool) (x y t : ℕ) :
    (Bool.rec (motive := fun _ => ℕ) y x c).testBit t = (if c then x.testBit t else y.testBit t) := by
  cases c <;> rfl

private theorem testBit_orN_anyF (f : ℕ → ℕ) (p : ℕ) : ∀ n,
    (orN n f).testBit p = (List.range n).any fun i => (f i).testBit p
  | 0 => by
    have e : orN 0 f = 0 := rfl
    rw [e]
    simp
  | n + 1 => by
    have e : orN (n + 1) f = f n ||| orN n f := rfl
    rw [e, Nat.testBit_or, testBit_orN_anyF f p n, List.range_succ, List.any_append]
    simp [Bool.or_comm]

private theorem testBit_ltF {x w j : ℕ} (hx : x < 2 ^ w) (hj : w ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hj))

private theorem bit_packM18 {r c : ℕ} (M : Array ℕ) (hr : r < 18) (hc : c < 18) :
    (packM 18 M).testBit (18 * r + c) = (M.getD r 0).testBit c := by
  rw [testBit_packM]
  have h1 : 18 * r + c < 18 * 18 := by omega
  have e1 : (18 * r + c) / 18 = r := by omega
  have e2 : (18 * r + c) % 18 = c := by omega
  simp [h1, e1, e2]

private theorem packM_zero8F : packM 8 CFSG.EvenSmallLie.UnitarySix.YamadaPar.zero8 = 0 := by
  decide

private theorem packM_foldl_msum2 (mask : ℕ) (f : ℕ → Array ℕ) : ∀ k,
    packM 8 ((List.range k).foldl (fun acc m => if mask.testBit m then bxor 8 acc (f m) else acc)
      CFSG.EvenSmallLie.UnitarySix.YamadaPar.zero8) = msumK k mask fun m => packM 8 (f m)
  | 0 => packM_zero8F
  | k + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have e : msumK (k + 1) mask (fun m => packM 8 (f m)) =
        Bool.rec (motive := fun _ => ℕ) (msumK k mask fun m => packM 8 (f m))
          (Nat.xor (packM 8 (f k)) (msumK k mask fun m => packM 8 (f m))) (bit mask k) := rfl
    rw [e, bit_eqF]
    cases h : mask.testBit k
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact packM_foldl_msum2 mask f k
    · simp only [↓reduceIte]
      rw [packM_bxor_proved, packM_foldl_msum2 mask f k]
      exact Nat.xor_comm _ _

theorem packM_msum2_proved (k mask : ℕ) (f : ℕ → Array ℕ) :
    packM 8 (msum2 k mask f) = msumK k mask fun m => packM 8 (f m) :=
  packM_foldl_msum2 mask f k

private theorem c2CL_spec : ∀ k < 16, getLD 0 c2CL k = CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2C k ∧
    CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2C k < 18 := by
  decide

private theorem c2IL_spec : ∀ c < 18, getLD 0 c2IL c = CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c := by
  decide

theorem blk2Bits_eq_proved (M : Array ℕ) : blk2Bits M = blk2K (packM 18 M) := by
  unfold blk2K
  rw [strictN_eq]
  apply Nat.eq_of_testBit_eq
  intro p
  rw [blk2Bits, testBit_bitsOf, testBit_orN_anyF]
  simp only [testBit_nIfF, pw2_eqF, Nat.testBit_two_pow]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
  have key : ∀ k < 32, bit (packM 18 M)
      (Nat.add (Bool.rec (motive := fun _ => ℕ) 162 0 (Nat.blt k 16)) (getLD 0 c2CL (Nat.mod k 16))) =
      (M.getD (if k < 16 then 0 else 9) 0).testBit
        (CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2C (k % 16)) := by
    intro k hk
    obtain ⟨h1, h2⟩ := c2CL_spec (k % 16) (Nat.mod_lt _ (by decide))
    rw [bit_eqF]
    change (packM 18 M).testBit (Bool.rec (motive := fun _ => ℕ) 162 0 (Nat.blt k 16) +
      getLD 0 c2CL (k % 16)) = _
    rw [h1]
    by_cases hk16 : k < 16
    · have : Nat.blt k 16 = true := by simpa using hk16
      rw [this]
      have := bit_packM18 M (r := 0) (by decide) h2
      simpa [hk16] using this
    · rw [blt_falseF hk16]
      have := bit_packM18 M (r := 9) (by decide) h2
      simpa [hk16] using this
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨p, hp, ?_⟩
    rw [key p hp, hb]
    simp
  · rintro ⟨k, hk, h⟩
    rw [key k hk] at h
    by_cases hb : (M.getD (if k < 16 then 0 else 9) 0).testBit
        (CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2C (k % 16)) = true
    · simp only [hb, ↓reduceIte] at h
      have hkp : k = p := of_decide_eq_true h
      subst hkp
      exact ⟨hk, hb⟩
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      simp at h

private noncomputable def emb2G (d c : ℕ) : ℕ :=
  if CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c < 16 then
    ((if d.testBit (CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c) then 2 ^ c else 0) |||
      (if d.testBit (16 + CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c) then 2 ^ (162 + c) else 0))
  else 0

private theorem emb2K_eq (d : ℕ) : emb2K d = orN 18 (emb2G d) := by
  unfold emb2K
  rw [strictN_eq]
  apply orN_congr
  intro c hc
  beta_reduce
  rw [c2IL_spec c hc, bit_eqF, bit_eqF, pw2_eqF, pw2_eqF, emb2G]
  by_cases h1 : CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c < 16
  · have hb : Nat.blt (CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c) 16 = true := by simpa using h1
    rw [hb, ite_eq_left h1]
    cases d.testBit (CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c) <;>
      cases d.testBit (Nat.add 16 (CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c)) <;> rfl
  · rw [blt_falseF h1, ite_eq_right h1]

private theorem testBit_emb2G (d c p : ℕ) : (emb2G d c).testBit p =
    (decide (CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c < 16) &&
      ((d.testBit (CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c) && decide (c = p)) ||
        (d.testBit (16 + CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c) && decide (162 + c = p)))) := by
  unfold emb2G
  by_cases h1 : CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c < 16
  · cases d.testBit (CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c) <;>
      cases d.testBit (16 + CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I c) <;>
      simp [h1, Nat.testBit_two_pow, Nat.testBit_or]
  · simp [h1]

theorem packM_emb2_proved (d : ℕ) : packM 18 (emb2Bits d) = emb2K d := by
  rw [emb2K_eq]
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_packM, testBit_orN_anyF]
  simp only [testBit_emb2G]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
    Bool.or_eq_true]
  have hrow : ∀ q < 18 * 18, ((emb2Bits d).getD (q / 18) 0).testBit (q % 18) =
      ((decide (q / 18 = 0) || decide (q / 18 = 9)) &&
        (decide (CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I (q % 18) < 16) &&
          d.testBit (if q / 18 = 0 then CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I (q % 18)
            else 16 + CFSG.EvenSmallLie.UnitarySix.YamadaN2.c2I (q % 18)))) := by
    intro q hq
    have hr : q / 18 < 18 := by omega
    have hc : q % 18 < 18 := Nat.mod_lt _ (by decide)
    simp only [emb2Bits, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hr, ↓reduceDIte,
      Option.getD_some]
    by_cases h0 : q / 18 = 0
    · simp [h0, testBit_bitsOf, hc]
    · by_cases h9 : q / 18 = 9
      · simp [h9, testBit_bitsOf, hc]
      · simp [h0, h9]
  constructor
  · rintro ⟨hp, hb⟩
    rw [hrow p hp] at hb
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hr, hc16, hd⟩ := hb
    have hcp := Nat.div_add_mod p 18
    rcases hr with hr | hr
    · rw [ite_eq_left hr] at hd
      refine ⟨p % 18, Nat.mod_lt _ (by decide), hc16, Or.inl ⟨hd, by omega⟩⟩
    · rw [ite_eq_right (by omega)] at hd
      refine ⟨p % 18, Nat.mod_lt _ (by decide), hc16, Or.inr ⟨hd, by omega⟩⟩
  · rintro ⟨c, hc, hc16, h⟩
    rcases h with ⟨hd, rfl⟩ | ⟨hd, rfl⟩
    · have hp : c < 18 * 18 := by omega
      refine ⟨hp, ?_⟩
      rw [hrow c hp]
      have e1 : c / 18 = 0 := Nat.div_eq_of_lt hc
      have e2 : c % 18 = c := Nat.mod_eq_of_lt hc
      simp [e1, e2, hc16, hd]
    · have hp : 162 + c < 18 * 18 := by omega
      refine ⟨hp, ?_⟩
      rw [hrow _ hp]
      have e1 : (162 + c) / 18 = 9 := by omega
      have e2 : (162 + c) % 18 = c := by omega
      simp [e1, e2, hc16, hd]

theorem par640_eq_proved (n : ℕ) : par640 n = parK 640 n := by
  have e : parK 640 n = Nat.rec (motive := fun _ => Bool) false
      (fun i acc => Bool.rec (motive := fun _ => Bool) acc (notB acc) (bit n i)) 640 := by
    unfold parK
    exact strictB_eqF n _
  rw [e, par640]
  have : ∀ w, xorFold w (fun i => n.testBit i) = Nat.rec (motive := fun _ => Bool) false
      (fun i acc => Bool.rec (motive := fun _ => Bool) acc (notB acc) (bit n i)) w := by
    intro w
    induction w with
    | zero => rfl
    | succ w ih =>
      rw [xorFold_succ, ih]
      change _ = Bool.rec (motive := fun _ => Bool) _ (notB _) (bit n w)
      rw [bit_eqF]
      cases n.testBit w <;> cases (Nat.rec (motive := fun _ => Bool) false
        (fun i acc => Bool.rec (motive := fun _ => Bool) acc (notB acc) (bit n i)) w) <;> rfl
  exact this 640

private theorem testBit_catW (w : ℕ) (hw : 0 < w) : ∀ (L : List ℕ) (p : ℕ),
    (CFSG.EvenSmallLie.UnitarySix.YamadaN2.catW w L).testBit p =
      (decide (p < w * L.length) && (L.getD (p / w) 0 % 2 ^ w).testBit (p % w))
  | [], p => by simp [CFSG.EvenSmallLie.UnitarySix.YamadaN2.catW]
  | a :: L, p => by
    rw [CFSG.EvenSmallLie.UnitarySix.YamadaN2.catW, Nat.testBit_or, Nat.testBit_shiftLeft,
      testBit_catW w hw L]
    by_cases hp : p < w
    · have e1 : p / w = 0 := Nat.div_eq_of_lt hp
      have e2 : p % w = p := Nat.mod_eq_of_lt hp
      have h3 : p < w * (L.length + 1) := by
        have : w ≤ w * (L.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have h4 : ¬ p ≥ w := by omega
      simp [hp, e1, e2, h3, h4]
    · obtain ⟨q, rfl⟩ : ∃ q, p = q + w := ⟨p - w, by omega⟩
      have h1 : (a % 2 ^ w).testBit (q + w) = false :=
        testBit_ltF (Nat.mod_lt _ (Nat.two_pow_pos w)) (by omega)
      have e1 : (q + w) / w = q / w + 1 := Nat.add_div_right q hw
      have e2 : (q + w) % w = q % w := Nat.add_mod_right q w
      have e3 : q + w - w = q := by omega
      have e4 : (q + w < w * (L.length + 1)) ↔ q < w * L.length := by
        rw [Nat.mul_succ]
        omega
      simp [h1, e1, e2, e3, e4]

theorem cat20_eq_proved (f : ℕ → ℕ) :
    CFSG.EvenSmallLie.UnitarySix.YamadaN2.cat20 f =
      orN 20 fun k => Nat.shiftLeft (Nat.mod (f k) (2 ^ 32)) (Nat.mul k 32) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [CFSG.EvenSmallLie.UnitarySix.YamadaN2.cat20, testBit_catW 32 (by decide), testBit_orN_anyF]
  simp only [List.length_map, List.length_range]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
  change _ ↔ ∃ k, k < 20 ∧ ((f k % 2 ^ 32) <<< (k * 32)).testBit p = true
  simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, hb⟩
    have hk : p / 32 < 20 := by omega
    refine ⟨p / 32, hk, by omega, ?_⟩
    have e : p - p / 32 * 32 = p % 32 := by omega
    rw [e]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk] at hb
    simpa using hb
  · rintro ⟨k, hk, hle, hb⟩
    have hlt : p - k * 32 < 32 := by
      apply Nat.lt_of_not_le
      intro hc
      rw [testBit_ltF (Nat.mod_lt _ (Nat.two_pow_pos 32)) hc] at hb
      exact absurd hb (by decide)
    have e1 : p / 32 = k := by omega
    have e2 : p % 32 = p - k * 32 := by omega
    refine ⟨by omega, ?_⟩
    rw [e1, e2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
    simpa using hb

theorem packM_foldl_bxor_proved (d : ℕ) (g : ℕ → Array ℕ) (init : Array ℕ) (L : List ℕ) :
    packM d (L.foldl (fun acc i => bxor d acc (g i)) init) =
      L.foldl (fun acc i => Nat.xor acc (packM d (g i))) (packM d init) := by
  induction L generalizing init with
  | nil => rfl
  | cons a L ih => simp only [List.foldl_cons, ih, packM_bxor_proved]

end CFSG.KC.U6F2

end
