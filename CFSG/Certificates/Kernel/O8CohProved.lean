module

public import Certificates.Data.Kernel.O8.CohK
public import CFSG.Certificates.Kernel.U6LinProved
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainModData
import CFSG.Certificates.Kernel.F2WordSound

public section

namespace CFSG.KC.O8Coh

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.U6F2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (bmul bxor btr unpackN packN bitsOf testBit_bitsOf)
open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

@[expose] def GenBind (ε : Eps) (G : List ℕ) : Prop :=
  ∀ s < 6, packM 6 (genRows ε s) = getLD 0 G s ∧
    ∀ r < 6, (genRows ε s).getD r 0 = fget (getLD 0 G s) r 6 ∧
      colBits (genRows ε s) r = colK (getLD 0 G s) r

private theorem testBit_fget6 (X i j : ℕ) :
    (fget X i 6).testBit j = (decide (j < 6) && X.testBit (i * 6 + j)) := by
  change ((X >>> (i * 6)) &&& maskN 6).testBit j = _
  rw [F2W.maskN_eq, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Bool.and_comm]

private theorem fget6_lt (X i : ℕ) : fget X i 6 < 2 ^ 6 := by
  change (X >>> (i * 6)) &&& maskN 6 < 2 ^ 6
  rw [F2W.maskN_eq, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos 6)

private theorem nIf_eq_ite (c : Bool) (a b : ℕ) :
    Bool.rec (motive := fun _ => ℕ) b a c = if c = true then a else b := by
  cases c <;> rfl

private theorem packM_zero6 : packM 6 zero6 = 0 := by decide

private theorem packM_id6 : packM 6 id6 = idK6 := by decide

private theorem packM_id6F : packM 6 id6 = idF 6 := by decide +kernel

theorem packM_combo6 (row : ℕ) (C : ℕ → Array ℕ) : ∀ k,
    packM 6 (combo6 row C k) = msumK k row fun d => packM 6 (C d)
  | 0 => by
    rw [combo6]
    exact packM_zero6
  | k + 1 => by
    have e : (msumK (k + 1) row fun d => packM 6 (C d)) =
        nIf(bit row k, Nat.xor (packM 6 (C k)) (msumK k row fun d => packM 6 (C d)),
          msumK k row fun d => packM 6 (C d)) := rfl
    rw [combo6, e, F2W.bit_eq, nIf_eq_ite]
    by_cases h : row.testBit k = true
    · rw [if_pos h, if_pos h, packM_bxor_proved, packM_combo6 row C k]
      exact Nat.xor_comm _ _
    · rw [if_neg h, if_neg h, packM_combo6 row C k]

theorem packM_diag6 (B : Array ℕ) : packM 6 (diag6 B) = Nat.land (packM 6 B) idK6 := by
  rw [← packM_id6]
  apply Nat.eq_of_testBit_eq
  intro p
  change _ = (packM 6 B &&& packM 6 id6).testBit p
  have hid : id6 = Array.ofFn (n := 6) fun r => 2 ^ (r : ℕ) := by decide
  rw [Nat.testBit_and, testBit_packM, testBit_packM, testBit_packM, hid]
  by_cases hp : p < 6 * 6
  · have hq : p / 6 < 6 := by omega
    simp [hp, hq, diag6, Array.getD_eq_getD_getElem?, Nat.testBit_and]
  · simp [hp]

theorem packM_outer6 (u w : ℕ) : packM 6 (outer6 u w) = outerK u w := by
  have e : outerK u w = orN 6 fun a =>
      (Bool.rec (motive := fun _ => ℕ) 0 (fget w 0 6) (bit u a)) <<< (6 * a) := rfl
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro p
  have hf : ∀ a < 6, Bool.rec (motive := fun _ => ℕ) 0 (fget w 0 6) (bit u a) < 2 ^ 6 := by
    intro a _
    cases bit u a
    · exact Nat.two_pow_pos 6
    · exact fget6_lt w 0
  rw [F2W.testBit_orN_fields hf, testBit_packM]
  by_cases hp : p < 6 * 6
  · have hq : p / 6 < 6 := by omega
    have hr : p % 6 < 6 := Nat.mod_lt _ (by decide)
    simp only [hp, decide_true, Bool.true_and, F2W.bit_eq, outer6, Array.getD_eq_getD_getElem?,
      Array.getElem?_ofFn, hq, ↓reduceDIte, Option.getD_some]
    cases u.testBit (p / 6)
    · simp
    · simp [testBit_fget6, hr]
  · simp [hp]

theorem packM_ite (c : Prop) [Decidable c] (A B : Array ℕ) :
    packM 6 (if c then A else B) = if c then packM 6 A else packM 6 B := by
  split <;> rfl

theorem cobFb6_eq {ε : Eps} {G : List ℕ} (hG : GenBind ε G) (v : ℕ) : cobFb6 ε v = cobK G v := by
  rw [cobFb6, packN_eq_proved]
  refine orN_congr fun s hs => ?_
  rw [packM_bxor_proved, packM_bmul_proved, packM_bmul_proved, packM_unpackN_proved, (hG s hs).1]
  all_goals rfl

theorem gamBlock_eq {ε : Eps} {G : List ℕ} (hG : GenBind ε G) (v : ℕ) {k : ℕ} (hk : k < 48) :
    packM 6 (gamBlock ε (unpackN 6 v) k) = gamBlockK G v k := by
  by_cases h6 : k < 6
  · have hb : Nat.blt k 6 = true := Nat.blt_eq ▸ h6
    rw [gamBlock, if_pos h6, gamBlockK, hb, packM_bxor_proved, packM_btr_proved,
      packM_unpackN_proved]
    all_goals rfl
  have hb6 : Nat.blt k 6 = false := Bool.eq_false_iff.2 fun h => h6 (Nat.blt_eq ▸ h)
  by_cases h12 : k < 12
  · have hb : Nat.blt k 12 = true := Nat.blt_eq ▸ h12
    rw [gamBlock, if_neg h6, if_pos h12, gamBlockK, hb6, hb, packM_diag6, packM_unpackN_proved]
    all_goals rfl
  have hb12 : Nat.blt k 12 = false := Bool.eq_false_iff.2 fun h => h12 (Nat.blt_eq ▸ h)
  have ha : (k - 12) / 6 < 6 := by omega
  have hr : (k - 12) % 6 < 6 := Nat.mod_lt _ (by decide)
  obtain ⟨hP, hR⟩ := hG _ ha
  have hrow := (hR _ hr).1
  rw [gamBlock, if_neg h6, if_neg h12, gamBlockK, hb6, hb12]
  simp only [packM_bxor_proved, packM_combo6, packM_bmul_proved, packM_btr_proved, packM_outer6,
    packM_unpackN_proved, getD_unpackN_proved v 6 ha, hP, hrow]
  all_goals rfl

theorem gamFb_eq {ε : Eps} {G : List ℕ} (hG : GenBind ε G) (v : ℕ) : gamFb ε v = gamK G v := by
  rw [gamFb, packN_eq_proved]
  refine orN_congr fun k hk => ?_
  rw [gamBlock_eq hG v hk]
  all_goals rfl

theorem modBlock_eq {ε : Eps} {G : List ℕ} (hG : GenBind ε G) (v : ℕ) {k : ℕ} (hk : k < 36) :
    packM 6 (modBlock ε (unpackN 6 v) k) =
      modBlockK (getLD 0 G (k / 6)) v (k / 6) (k % 6) := by
  have hi : k / 6 < 6 := by omega
  have hl : k % 6 < 6 := Nat.mod_lt _ (by decide)
  obtain ⟨hP, hR⟩ := hG _ hi
  have hcol := (hR _ hl).2
  rw [modBlock, modBlockK]
  simp only [packM_bxor_proved, packM_combo6, packM_bmul_proved, packM_unpackN_proved, packM_ite,
    packM_zero6, getD_unpackN_proved v 6 hi, hP, hcol, F2W.bit_eq, nIf_eq_ite]
  all_goals rfl

theorem modFb_eq {ε : Eps} {G : List ℕ} (hG : GenBind ε G) (v : ℕ) : modFb ε v = modK G v := by
  rw [modFb, packN_eq_proved]
  refine orN_congr fun k hk => ?_
  rw [modBlock_eq hG v hk]
  all_goals rfl

theorem urPair6_eq (ε : Eps) (C : ℕ → Array ℕ) (w : List ℕ) :
    urPair6 ε C w = urPairG 6 id6 zero6 (genRows ε) C w := by
  induction w with
  | nil => rfl
  | cons s w ih => simp only [urPair6, urPairG, ih]

theorem extFb_eq {ε : Eps} {G : List ℕ} (hG : GenBind ε G)
    (hl : ∀ w ∈ extRels ε, ∀ s ∈ w, s < 6) (v : ℕ) :
    extFb ε v = extK G (nRels ε) (extRels ε) v := by
  rw [extFb, packN_eq_proved]
  refine orN_congr fun k hk => ?_
  have hw : ∀ s ∈ (extRels ε).getD k [], s < 6 := by
    intro s hs
    by_cases h : k < (extRels ε).length
    · rw [List.getD_eq_getElem _ _ h] at hs
      exact hl _ (List.getElem_mem h) s hs
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)] at hs
      simp at hs
  have hC : ∀ s ∈ (extRels ε).getD k [],
      getLD 0 ((List.range 6).map fun s => blk v s) s = packM 6 (unpackN 6 v s) := by
    intro s hs
    rw [getLD_map_range _ _ (hw s hs), packM_unpackN_proved]
    all_goals rfl
  rw [urPair6_eq, getLD_eq_getD [] (extRels ε) k,
    urPairK_eq_proved (I := id6) (Z := zero6) (gen := genRows ε) (C := unpackN 6 v)
      (fun s hs => ((hG s (hw s hs)).1).symm) hC packM_id6F packM_zero6]
  rw [shiftRight_lor_shiftLeft (packM_lt_proved 6 _)]
  all_goals rfl

end CFSG.KC.O8Coh

end
