module

public import CFSG.Certificates.Kernel.O8EnumDefs
public import Certificates.Data.Kernel.O8.NodeM
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitFix
import CFSG.Certificates.Kernel.O8MulProved
import CFSG.Certificates.Kernel.O8VecProved
import CFSG.Certificates.Kernel.O8PopcProved

public section

set_option exponentiation.threshold 4096

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.N3Split

private theorem strictN_eq'' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

private theorem testBit_orN'' (f : ℕ → ℕ) (p : ℕ) : ∀ n,
    (orN n f).testBit p = (List.range n).any fun i => (f i).testBit p
  | 0 => by
    have e : orN 0 f = 0 := rfl
    rw [e]
    simp
  | n + 1 => by
    have e : orN (n + 1) f = f n ||| orN n f := rfl
    rw [e, Nat.testBit_or, testBit_orN'' f p n, List.range_succ, List.any_append]
    simp [Bool.or_comm]

private theorem testBit_xorN'' (f : ℕ → ℕ) (p : ℕ) : ∀ n,
    (xorN n f).testBit p = xorFold n fun l => (f l).testBit p
  | 0 => by
    have e : xorN 0 f = 0 := rfl
    rw [e]
    simp [xorFold]
  | n + 1 => by
    have e : xorN (n + 1) f = f n ^^^ xorN n f := rfl
    rw [e, Nat.testBit_xor, xorFold_succ, testBit_xorN'' f p n, Bool.xor_comm]

private theorem xorFold_congr'' {k : ℕ} {f g : ℕ → Bool} (h : ∀ l < k, f l = g l) :
    xorFold k f = xorFold k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [xorFold_succ, xorFold_succ, ih (fun l hl => h l (by omega)), h k (by omega)]

private theorem xorFold_xor (f g : ℕ → Bool) : ∀ k,
    xorFold k (fun j => f j ^^ g j) = (xorFold k f ^^ xorFold k g)
  | 0 => rfl
  | k + 1 => by
    rw [xorFold_succ, xorFold_succ, xorFold_succ, xorFold_xor f g k]
    cases xorFold k f <;> cases xorFold k g <;> cases f k <;> cases g k <;> rfl

private theorem xorFold_single (i : ℕ) (g : ℕ → Bool) : ∀ k,
    xorFold k (fun j => decide (i = j) && g j) = (decide (i < k) && g i)
  | 0 => by simp [xorFold]
  | k + 1 => by
    rw [xorFold_succ, xorFold_single i g k]
    by_cases h : i < k
    · have h1 : i ≠ k := by omega
      have h2 : i < k + 1 := by omega
      simp [h, h1, h2]
    · by_cases h2 : i = k
      · subst h2
        simp
      · have h3 : ¬ i < k + 1 := by omega
        simp [h, h2, h3]

private theorem pw2_eq' (w : ℕ) : pw2 w = 2 ^ w := by
  rw [pw2]
  change 1 <<< w = 2 ^ w
  rw [Nat.shiftLeft_eq, Nat.one_mul]

private theorem maskN_eq' (w : ℕ) : maskN w = 2 ^ w - 1 := by
  rw [maskN, ← pw2_eq']
  rfl

private theorem testBit_nIf (c : Bool) (x t : ℕ) :
    (Bool.rec (motive := fun _ => ℕ) 0 x c).testBit t = (c && x.testBit t) := by
  cases c <;> simp

private theorem beq_bitN' (x q : ℕ) : Nat.beq (bitN x q) 1 = x.testBit q := by
  have e : bitN x q = (x >>> q) % 2 := by
    change (x >>> q) &&& 1 = _
    rw [Nat.and_one_is_mod]
  have h2 : x.testBit q = decide ((x >>> q) % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
  rw [e, h2]
  rcases Nat.mod_two_eq_zero_or_one (x >>> q) with h | h
  · rw [h]
    rfl
  · rw [h]
    rfl

private theorem testBit_row12'' (b l r : ℕ) :
    (row12 b l).testBit r = (decide (r < 12) && b.testBit (12 * l + r)) := by
  unfold row12 fget
  have e : maskN 12 = 2 ^ 12 - 1 := by decide
  change ((b >>> (l * 12)) &&& maskN 12).testBit r = _
  rw [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, mul_comm l]
  cases decide (r < 12) <;> simp

private theorem testBit_rowsOf'' (a i r : ℕ) (hi : i < 12) :
    ((rowsOf a).getD i 0).testBit r = (decide (r < 12) && a.testBit (12 * i + r)) := by
  have e : (rowsOf a).getD i 0 = (a >>> (12 * i)) % 2 ^ 12 := by
    simp [rowsOf, Array.getD_eq_getD_getElem?, hi]
  rw [e, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

private theorem mod_lt_iff (v j : ℕ) : decide (v % 2 ^ (j + 1) < 2 ^ j) = !v.testBit j := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.mod_pow_succ]
  have h1 : v % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ j) with h | h
  · rw [h]
    simp [h1]
  · rw [h]
    simp

private theorem testBit_A_xor_sw {j v : ℕ} (hj : j < 12) (hv : v < 4096) :
    (2 ^ 4096 - 1 ^^^ swarK.getD j 0).testBit v = v.testBit j := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, testBit_swarK_proved hj, mod_lt_iff]
  simp [hv]

private theorem testBit_mulVecK (y v i : ℕ) (hi : i < 12) :
    (mulVecK y v).testBit i = xorFold 12 fun j => (row12 y i).testBit j && v.testBit j := by
  rw [mulVecK, bmulVec, testBit_bitsOf]
  simp only [hi, decide_true, Bool.true_and]
  apply xorFold_congr''
  intro j hj
  rw [testBit_rowsOf'' y i j hi, testBit_row12'']

theorem fixMaskW_lt_proved (y : ℕ) : fixMaskW swarK y < 2 ^ 4096 := by
  apply Nat.lt_pow_two_of_testBit
  intro p hp
  rw [fixMaskW, strictN_eq'', maskN_eq']
  change (2 ^ 4096 - 1 ^^^ (2 ^ 4096 - 1 &&& _)).testBit p = false
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  have : ¬ p < 4096 := by omega
  simp [this]

theorem testBit_fixMaskW_proved (y : ℕ) {v : ℕ} (hv : v < 4096) :
    (fixMaskW swarK y).testBit v = (mulVec12K y v == v) := by
  rw [fixMaskW, strictN_eq'', maskN_eq']
  change (2 ^ 4096 - 1 ^^^ (2 ^ 4096 - 1 &&& _)).testBit v = _
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one, testBit_orN'']
  simp only [hv, decide_true, Bool.true_and]
  have key : ∀ i < 12, (xorN 12 fun j =>
      Bool.rec (motive := fun _ => ℕ) 0 (Nat.xor (2 ^ 4096 - 1) (swarK.getD j 0))
        (Nat.beq (bitN (Nat.xor (row12 y i) (pw2 i)) j) 1)).testBit v =
      ((mulVecK y v).testBit i ^^ v.testBit i) := by
    intro i hi
    rw [testBit_xorN'', testBit_mulVecK y v i hi]
    have e : ∀ j < 12, (Bool.rec (motive := fun _ => ℕ) 0 (Nat.xor (2 ^ 4096 - 1) (swarK.getD j 0))
        (Nat.beq (bitN (Nat.xor (row12 y i) (pw2 i)) j) 1)).testBit v =
        (((row12 y i).testBit j && v.testBit j) ^^ (decide (i = j) && v.testBit j)) := by
      intro j hj
      rw [testBit_nIf, beq_bitN']
      change ((row12 y i ^^^ pw2 i).testBit j && (2 ^ 4096 - 1 ^^^ swarK.getD j 0).testBit v) = _
      rw [testBit_A_xor_sw hj hv, Nat.testBit_xor, pw2_eq', Nat.testBit_two_pow]
      cases (row12 y i).testBit j <;> cases decide (i = j) <;> cases v.testBit j <;> rfl
    rw [xorFold_congr'' e, xorFold_xor, xorFold_single]
    simp [hi]
  have hany : ((List.range 12).any fun i => (xorN 12 fun j =>
      Bool.rec (motive := fun _ => ℕ) 0 (Nat.xor (2 ^ 4096 - 1) (swarK.getD j 0))
        (Nat.beq (bitN (Nat.xor (row12 y i) (pw2 i)) j) 1)).testBit v) =
      (List.range 12).any fun i => ((mulVecK y v).testBit i ^^ v.testBit i) := by
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, List.mem_range]
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, by rw [← key i hi]; exact h⟩
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, by rw [key i hi]; exact h⟩
  rw [hany, ← mulVecK_eq_proved]
  apply Bool.eq_iff_iff.2
  simp only [Bool.true_xor, Bool.not_eq_true', List.any_eq_false, List.mem_range, beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 12
    · have := h i hi
      cases h1 : (mulVecK y v).testBit i <;> cases h2 : v.testBit i <;> simp_all
    · have h1 : (mulVecK y v).testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (mulVecK_lt y v)
          (by
            have : 2 ^ 12 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
            simpa using this))
      have h2 : v.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
          (by
            have : 2 ^ 12 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
            simpa using this))
      rw [h1, h2]
  · intro h i _
    rw [h]
    simp

theorem fixCountF_eqM_proved {SW : List ℕ} (hSW : SW = swarK) (k : ℕ) :
    fixCountF k = popcM SW (fixMaskW SW k) := by
  subst hSW
  rw [popcM_swarK_proved (fixMaskW_lt_proved k), fixCountF, fixVecs_eq_proved]
  have e : ((List.range 4096).filter fun v => (fixMaskW swarK k).testBit v) =
      (List.range 4096).filter fun v => mulVec12K k v == v :=
    List.filter_congr fun v hv => testBit_fixMaskW_proved k (List.mem_range.1 hv)
  rw [e]

theorem fixBoth_eqM_proved {SW : List ℕ} (hSW : SW = swarK) (s c : ℕ) :
    ((fixVecs s).filter fun v => mulVecK c v == v).length =
      popcM SW (fixMaskW SW s &&& fixMaskW SW c) := by
  subst hSW
  rw [popcM_swarK_proved (Nat.and_lt_two_pow _ (fixMaskW_lt_proved c)), fixVecs_eq_proved,
    List.filter_filter]
  have e : ((List.range 4096).filter fun v => (fixMaskW swarK s &&& fixMaskW swarK c).testBit v) =
      (List.range 4096).filter fun v => (mulVecK c v == v) && (mulVec12K s v == v) := by
    apply List.filter_congr
    intro v hv
    have hv' := List.mem_range.1 hv
    rw [Nat.testBit_and, testBit_fixMaskW_proved s hv', testBit_fixMaskW_proved c hv',
      mulVecK_eq_proved, Bool.and_comm]
  rw [e]

private theorem filter_mask (X y : ℕ) :
    (((List.range 4096).filter fun v => X.testBit v).filter fun v => mulVecK y v == v) =
      (List.range 4096).filter fun v => (Nat.land X (fixMaskW swarK y)).testBit v := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro v hv
  change _ = (X &&& fixMaskW swarK y).testBit v
  rw [Nat.testBit_and, testBit_fixMaskW_proved y (List.mem_range.1 hv), mulVecK_eq_proved,
    Bool.and_comm]

private theorem newGen_eqM (span : List ℕ) (y : ℕ) : newGen span y = newGenM span y := by
  simp only [newGen, newGenM, mulK_eq_proved]

private theorem node_eqM (B : ℕ) : ∀ (fuel : ℕ) (span : List ℕ) (X : ℕ) (rest : List ℕ),
    X < 2 ^ 4096 →
      node B fuel span ((List.range 4096).filter fun v => X.testBit v) rest =
        nodeM B swarK fuel span X rest
  | 0, _, _, _, _ => rfl
  | fuel + 1, span, X, rest, hX => by
    rw [node, nodeM, popcM_swarK_proved hX]
    congr 1
    congr 1
    funext l
    match l with
    | [] => rfl
    | y :: ys =>
      simp only []
      rw [newGen_eqM, filter_mask X y, node_eqM B fuel _ (Nat.land X (fixMaskW swarK y)) _
        (Nat.and_lt_two_pow _ (fixMaskW_lt_proved y))]
      have hm : mulK y = mul12K y := funext (mulK_eq_proved y)
      rw [hm]
      simp only [mulK_eq_proved]

theorem allRoots_eqM_proved {B : ℕ} {SW I : List ℕ} {b : ℕ → Bool} {Xb : ℕ} (hSW : SW = swarK)
    (_hXb : Xb < 2 ^ 4096) (hb : ∀ v < 4096, Xb.testBit v = b v) :
    allRoots B I ((List.range 4096).filter b) =
      I.all fun r => nodeM B SW 8 [ID12, r] (Nat.land Xb (fixMaskW SW r)) (commOfK I r) := by
  subst hSW
  unfold allRoots
  refine congrArg (List.all I) (funext fun r => ?_)
  have hbase : (List.range 4096).filter b = (List.range 4096).filter fun v => Xb.testBit v := by
    apply List.filter_congr
    intro v hv
    rw [hb v (List.mem_range.1 hv)]
  have hC : commOf I r = commOfK I r := by
    simp only [commOf, commOfK, mulK_eq_proved]
  rw [rootCheck, hbase, filter_mask, idK_eq, hC,
    node_eqM B 8 _ (Nat.land Xb (fixMaskW swarK r)) _ (Nat.and_lt_two_pow _ (fixMaskW_lt_proved r))]

end CFSG.KC.O8

end
