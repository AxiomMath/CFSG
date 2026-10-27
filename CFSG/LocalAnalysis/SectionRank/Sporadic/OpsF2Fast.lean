module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.SectionRank.F2Fast

public section

namespace CFSG.SectionRank

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.Native Finset
open scoped Matrix

variable {d : ℕ}

theorem foldl_xor_toVecD' (g : ℕ → ℕ) (m init : ℕ) :
    toVecD d ((List.range m).foldl (fun acc i => acc ^^^ g i) init) =
      toVecD d init + ∑ i ∈ range m, toVecD d (g i) := by
  induction m generalizing init with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, sum_range_succ,
      ← add_assoc, toVecD_xor, ih]

theorem foldl_toVecD_of_step (F : ℕ → ℕ → ℕ) (h : ℕ → Fin d → ZMod 2)
    (hF : ∀ acc l, toVecD d (F acc l) = toVecD d acc + h l) (m init : ℕ) :
    toVecD d ((List.range m).foldl F init) = toVecD d init + ∑ l ∈ range m, h l := by
  induction m generalizing init with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, sum_range_succ,
      ← add_assoc, hF, ih]

omit d in
theorem sum_range_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∀ n : ℕ, ∑ l ∈ range n, ∑ i ∈ range k, f (k * l + i) = ∑ j ∈ range (k * n), f j
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, sum_range_blocks f k n, Nat.mul_succ, sum_range_add]

theorem toVecD_frEntry (Y : Array ℕ) (k c : ℕ) :
    toVecD d (frEntry Y k c) =
      ∑ i ∈ range 8, if c.testBit i then toVecD d (Y[8 * k + i]?.getD 0) else 0 := by
  unfold frEntry
  rw [foldl_xor_toVecD d (fun i => c.testBit i = true), toVecD_zero, zero_add]

theorem frTable_getD (nb : ℕ) (Y : Array ℕ) {t : ℕ} (ht : t < nb * 256) :
    (frTable nb Y)[t]?.getD 0 = frEntry Y (t / 256) (t % 256) := by
  unfold frTable
  rw [Array.getElem?_ofFn]
  simp [ht]

theorem testBit_byte (x l b i : ℕ) (hb : b < 4) (hi : i < 8) :
    ((((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256).testBit i =
      x.testBit (32 * l + 8 * b + i) := by
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    show (4294967296 : ℕ) = 2 ^ 32 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  have h1 : 8 * b + i < 32 := by omega
  simp [hi, h1, Nat.add_assoc]

theorem toVecD_frApply {nw : ℕ} (Y : Array ℕ) (hY : Y.size ≤ d) (hd : d ≤ 32 * nw) (x : ℕ) :
    toVecD d (frApply nw (frTable (4 * nw) Y) x) = toVecD d (vecMulN d Y x) := by
  set f : ℕ → Fin d → ZMod 2 :=
    fun j => if x.testBit j then toVecD d (Y[j]?.getD 0) else 0 with hf
  have hentry : ∀ l b, l < nw → b < 4 →
      toVecD d ((frTable (4 * nw) Y)[256 * (4 * l + b) +
        (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256]?.getD 0) =
        ∑ i ∈ range 8, f (8 * (4 * l + b) + i) := by
    intro l b hl hb
    have hc : (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256 < 256 :=
      Nat.mod_lt _ (by norm_num)
    rw [frTable_getD _ _ (by nlinarith), toVecD_frEntry]
    have e1 : (256 * (4 * l + b) + (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256) / 256 =
        4 * l + b := by omega
    have e2 : (256 * (4 * l + b) + (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256) % 256 =
        (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256 := by omega
    rw [e1, e2]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [testBit_byte x l b i hb hi, show 32 * l + 8 * b + i = 8 * (4 * l + b) + i by ring]
  have hfold : toVecD d (frApply nw (frTable (4 * nw) Y) x) =
      ∑ l ∈ range nw, ∑ b ∈ range 4, ∑ i ∈ range 8, f (8 * (4 * l + b) + i) := by
    have := foldl_toVecD_of_step (d := d) (fun acc l =>
        (List.range 4).foldl (fun acc b => acc ^^^ ((frTable (4 * nw) Y)[256 * (4 * l + b) +
          (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256]?.getD 0)) acc)
      (fun l => ∑ b ∈ range 4, toVecD d ((frTable (4 * nw) Y)[256 * (4 * l + b) +
          (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256]?.getD 0))
      (fun acc l => foldl_xor_toVecD' _ 4 acc) nw 0
    refine this.trans ?_
    rw [toVecD_zero, zero_add]
    refine sum_congr rfl fun l hl => sum_congr rfl fun b hb => ?_
    exact hentry l b (mem_range.1 hl) (mem_range.1 hb)
  have hblocks : ∑ l ∈ range nw, ∑ b ∈ range 4, ∑ i ∈ range 8, f (8 * (4 * l + b) + i) =
      ∑ j ∈ range (32 * nw), f j := by
    have inner : ∀ l, ∑ b ∈ range 4, ∑ i ∈ range 8, f (8 * (4 * l + b) + i) =
        ∑ i ∈ range 32, f (32 * l + i) := by
      intro l
      rw [show (32 : ℕ) = 8 * 4 by norm_num, ← sum_range_blocks (fun i => f (8 * 4 * l + i)) 8 4]
      refine sum_congr rfl fun b _ => sum_congr rfl fun i _ => ?_
      congr 1
      ring
    rw [sum_congr rfl fun l _ => inner l, sum_range_blocks f 32 nw]
  have htail : ∑ j ∈ range (32 * nw), f j = ∑ j ∈ range d, f j := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hd
    rw [hm, sum_range_add]
    have : ∑ j ∈ range m, f (d + j) = 0 := by
      refine sum_eq_zero fun j _ => ?_
      rw [hf]
      simp only
      rw [Array.getElem?_eq_none (by omega), Option.getD_none, toVecD_zero, ite_self]
    rw [this, add_zero]
  rw [hfold, hblocks, htail]
  unfold vecMulN
  rw [foldl_xor_toVecD d (fun j => x.testBit j = true), toVecD_zero, zero_add]

theorem rowsMatrix_frMul (X Y : Array ℕ) (hY : Y.size ≤ d) :
    rowsMatrix d (frMul d X Y) = rowsMatrix d X * rowsMatrix d Y := by
  rw [← rowsMatrix_mulRows]
  ext i k
  rw [rowsMatrix_apply, rowsMatrix_apply]
  unfold frMul mulRows
  rw [Array.getElem?_map, Array.getElem?_map]
  cases X[i.val]? with
  | none => rfl
  | some x =>
    simp only [Option.map_some, Option.getD_some]
    rw [toVecD_frApply Y hY (by omega)]

@[expose] noncomputable def spec2fr (d : ℕ) : OpsSpec (ops2fr d) 2 d where
  toMat := rowsMatrix d
  toVec := toVecD d
  WF X := X.size = d
  VWF _ := True
  decode_wf s := by simp [ops2fr, rowsOfPayload]
  toMat_decode s := rowsMatrix_rowsOfPayload d s
  mul_wf hX _ := by simp [ops2fr, frMul, hX]
  toMat_mul _ hY := rowsMatrix_frMul _ _ (le_of_eq hY)
  one_wf := by simp [ops2fr, idRows]
  toMat_one := rowsMatrix_idRows d
  toMat_eq _ _ h := by rw [beq_iff_eq.1 h]
  vmul_wf _ _ := trivial
  toVec_vmul _ _ := toVecD_vecMulN d _ _
  unit_wf _ := trivial
  toVec_ne {u w} h := (spec2 d).toVec_ne h

end CFSG.SectionRank
