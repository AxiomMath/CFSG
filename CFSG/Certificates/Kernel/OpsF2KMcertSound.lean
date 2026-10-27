module

public import Certificates.Data.Kernel.OpsF2KMcert
public import Certificates.Data.CFSGNative.SectionRank.F2Fast
import all CFSG.Certificates.Kernel.LocalCompCubSound
import CFSG.Certificates.Kernel.Co1BMulSound
import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.KC.Co1F2 (unpackR bind_sound)
open CFSG.KC.F2W (mulRows_unpackR vecMulN_unpackR vmF_lt)

private theorem mStepK_eq_cub (d : Nat) : stepK d = CFSG.KC.LocalComp.Cub.stepK d := by
  funext R op
  cases op <;> rfl

private theorem mExpOK_eq_cub : expOK = CFSG.KC.LocalComp.Cub.expOK := by
  funext op
  cases op <;> rfl

private theorem mRunK_eq_cub (d A B n : Nat) (prog : List Op) :
    runK d A B n prog =
      prog.foldl (CFSG.KC.LocalComp.Cub.stepK d) (CFSG.KC.LocalComp.Cub.initK d A B n) := by
  unfold runK
  rw [mStepK_eq_cub]
  rfl

private theorem mRegs_get {d A B n : Nat} {csA csB : List Char} {sA sB : String} {prog : List Op}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : sA = String.ofList csA) (hsB : sB = String.ofList csB)
    (hprog : prog.all (Op.lt n) = true) (hexp : prog.all expOK = true) {r : Nat} (hr : r < n) :
    ((ops2 d).run prog ((ops2 d).initRegs ((ops2 d).decode sA) ((ops2 d).decode sB) n))[r]! =
      unpackR d (getR d (runK d A B n prog) r) := by
  have eA : (ops2 d).decode sA = unpackR d A := by
    change CFSG.Sporadic.SmallF2.Native.rowsOfPayload d sA = _
    rw [hsA]
    exact bind_sound hA
  have eB : (ops2 d).decode sB = unpackR d B := by
    change CFSG.Sporadic.SmallF2.Native.rowsOfPayload d sB = _
    rw [hsB]
    exact bind_sound hB
  rw [eA, eB]
  have hinitlen : (CFSG.KC.LocalComp.Cub.initK d A B n).length = n := by
    simp [CFSG.KC.LocalComp.Cub.initK]
  have hinitsize : ((ops2 d).initRegs (unpackR d A) (unpackR d B) n).size = n := by
    simp [Ops.initRegs]
  have hexp' : prog.all CFSG.KC.LocalComp.Cub.expOK = true := by
    rw [← mExpOK_eq_cub]
    exact hexp
  have hmap := CFSG.KC.LocalComp.Cub.run_map hinitlen hinitsize
    (CFSG.KC.LocalComp.Cub.map_initK d A B n) hprog hexp'
  have hlen := CFSG.KC.LocalComp.Cub.length_stepK_foldl d n prog _ hinitlen
  have hsize := CFSG.KC.LocalComp.Cub.size_run d n prog _ hinitsize
  rw [mRunK_eq_cub]
  exact (CFSG.KC.LocalComp.Cub.getR_map hlen hsize hmap hr).symm

private theorem unpackR_mulF (d X Y : Nat) :
    unpackR d (mulF d X Y) = (ops2 d).mul (unpackR d X) (unpackR d Y) :=
  (mulRows_unpackR d X Y).symm

private theorem unpackR_idF_eq_one (d : Nat) : unpackR d (idF d) = (ops2 d).one :=
  CFSG.KC.LocalComp.Cub.unpackR_idF d

private theorem unpackR_powK {d X e : Nat} (he : e < 2 ^ 16) :
    unpackR d (powK d X e) = (ops2 d).pow (unpackR d X) e :=
  CFSG.KC.LocalComp.Cub.unpackR_powF16 he

private theorem eq_of_beq {d X Y : Nat} (h : Nat.beq X Y = true) :
    (ops2 d).eq (unpackR d X) (unpackR d Y) = true :=
  CFSG.KC.LocalComp.Cub.ops2_eq_unpackR h

private theorem commOK_of_commK {d X Y : Nat} (h : commK d X Y = true) :
    (ops2 d).commOK (unpackR d X) (unpackR d Y) = true := by
  unfold commK at h
  unfold Ops.commOK
  rw [← unpackR_mulF, ← unpackR_mulF]
  exact eq_of_beq h

private theorem conjOK_of_conjK {d H X W : Nat} (h : conjK d H X W = true) :
    (ops2 d).conjOK (unpackR d H) (unpackR d X) (unpackR d W) = true := by
  unfold conjK at h
  unfold Ops.conjOK
  rw [← unpackR_mulF, ← unpackR_mulF]
  exact eq_of_beq h

private theorem vmul_unpackR (d X v : Nat) : (ops2 d).vmul v (unpackR d X) = vmF d X v :=
  vecMulN_unpackR d X v

private theorem unit_eq (d k : Nat) : (ops2 d).unit k = CFSG.KLie.CT.pw2 k := rfl

private theorem pw2_lt {d k : Nat} (hk : k < d) : CFSG.KLie.CT.pw2 k < 2 ^ d := by
  rw [show CFSG.KLie.CT.pw2 k = 2 ^ k from Nat.one_shiftLeft k]
  exact Nat.pow_lt_pow_right (by norm_num) hk

private theorem vne_of_beq {d u w : Nat} (hu : u < 2 ^ d) (hw : w < 2 ^ d)
    (h : (!Nat.beq u w) = true) : (ops2 d).vne u w = true := by
  rw [CFSG.KC.LocalComp.Cub.vne_eq, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hw]
  exact h

private theorem wordLt_of_K {n : Nat} {w : Word} (h : wordLtK n w = true) : wordLt n w = true := by
  unfold wordLtK at h
  unfold wordLt
  rw [List.all_eq_true] at h ⊢
  intro p hp
  have := h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this ⊢
  exact this.1

private theorem evalW_unpackR {d n : Nat} {Rl : List Nat} {Ra : Array (Array Nat)}
    (hreg : ∀ r < n, Ra[r]! = unpackR d (getR d Rl r)) :
    ∀ w : Word, wordLtK n w = true → evalW (ops2 d) Ra w = unpackR d (evalWK d Rl w)
  | [], _ => (unpackR_idF_eq_one d).symm
  | (r, e) :: w, h => by
    unfold wordLtK at h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hr, he⟩, hw⟩ := h
    have hw' : wordLtK n w = true := by unfold wordLtK; exact hw
    rw [evalW, evalWK, unpackR_mulF, unpackR_powK (by omega), hreg r hr,
      evalW_unpackR hreg w hw']

private theorem factOK_of_K {d n : Nat} {Rl : List Nat} {Ra : Array (Array Nat)}
    (hreg : ∀ r < n, Ra[r]! = unpackR d (getR d Rl r)) :
    ∀ f : MFact, factK d Rl n f = true → factOK (ops2 d) Ra n f = true
  | .ord r e, h => by
    simp only [factK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hr, he⟩, he16⟩, hb⟩ := h
    simp only [factOK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hr, he⟩, ?_⟩
    rw [hreg r hr, ← unpackR_powK (by omega), ← unpackR_idF_eq_one]
    exact eq_of_beq hb
  | .conj h u w, hf => by
    simp only [factK, Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨⟨⟨hh, hu⟩, hw⟩, hb⟩ := hf
    simp only [factOK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hh, wordLt_of_K hu⟩, wordLt_of_K hw⟩, ?_⟩
    rw [hreg h hh, evalW_unpackR hreg u hu, evalW_unpackR hreg w hw, ← unpackR_mulF,
      ← unpackR_mulF]
    exact eq_of_beq hb
  | .ne w₁ w₂ t, hf => by
    simp only [factK, Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨⟨⟨h1, h2⟩, ht⟩, hb⟩ := hf
    simp only [factOK, Bool.and_eq_true]
    refine ⟨⟨wordLt_of_K h1, wordLt_of_K h2⟩, ?_⟩
    rw [evalW_unpackR hreg w₁ h1, evalW_unpackR hreg w₂ h2, unit_eq, vmul_unpackR, vmul_unpackR]
    exact vne_of_beq (vmF_lt _ _ _) (vmF_lt _ _ _) hb
  | .eq w₁ w₂, hf => by
    simp only [factK, Bool.and_eq_true] at hf
    obtain ⟨⟨h1, h2⟩, hb⟩ := hf
    simp only [factOK, Bool.and_eq_true]
    refine ⟨⟨wordLt_of_K h1, wordLt_of_K h2⟩, ?_⟩
    rw [evalW_unpackR hreg w₁ h1, evalW_unpackR hreg w₂ h2]
    exact eq_of_beq hb

theorem mcertCheck_of_K {d A B : Nat} {csA csB : List Char} {sA sB : String} {C : MCert}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : sA = String.ofList csA) (hsB : sB = String.ofList csB)
    (h : mcertK d A B C = true) : mcertCheck (ops2 d) sA sB C = true := by
  simp only [mcertK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, hexp⟩, hn⟩, hprog⟩, hfacts⟩ := h
  have hreg : ∀ r < C.nregs, ((ops2 d).regsOf sA sB C.nregs C.prog)[r]! =
      unpackR d (getR d (runK d A B C.nregs C.prog) r) :=
    fun r hr => mRegs_get hA hB hsA hsB hprog hexp hr
  unfold mcertCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hn, hprog⟩, ?_⟩
  rw [List.all_eq_true] at hfacts ⊢
  exact fun f hf => factOK_of_K hreg f (hfacts f hf)

theorem fusCheck_of_K {d A B nregs : Nat} {csA csB : List Char} {sA sB : String}
    {prog : List Op} {D : CFSG.RankThree.PartOne.CTP.Fus.Spec}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : sA = String.ofList csA) (hsB : sB = String.ofList csB)
    (h : fusK d A B nregs prog D = true) :
    CFSG.RankThree.PartOne.CTP.Fus.fusCheck (ops2 d) sA sB nregs prog D = true := by
  simp only [fusK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hm, hrA⟩, hrB⟩, hbA⟩, hbB⟩, hwf⟩ := h
  have hm' := hm
  simp only [mcertK, Bool.and_eq_true, decide_eq_true_eq] at hm'
  obtain ⟨⟨⟨⟨-, hexp⟩, -⟩, hprog⟩, -⟩ := hm'
  have hreg : ∀ r < nregs, ((ops2 d).regsOf sA sB nregs prog)[r]! =
      unpackR d (getR d (runK d A B nregs prog) r) :=
    fun r hr => mRegs_get hA hB hsA hsB hprog hexp hr
  have eA : (ops2 d).decode sA = unpackR d A := by
    change CFSG.Sporadic.SmallF2.Native.rowsOfPayload d sA = _
    rw [hsA]
    exact bind_sound hA
  have eB : (ops2 d).decode sB = unpackR d B := by
    change CFSG.Sporadic.SmallF2.Native.rowsOfPayload d sB = _
    rw [hsB]
    exact bind_sound hB
  unfold CFSG.RankThree.PartOne.CTP.Fus.fusCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨mcertCheck_of_K hA hB hsA hsB hm, hrA⟩, hrB⟩, ?_⟩, ?_⟩, hwf⟩
  · rw [hreg _ hrA, eA]
    exact eq_of_beq hbA
  · rw [hreg _ hrB, eB]
    exact eq_of_beq hbB

open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native in
theorem e8Check_of_K {d A B : Nat} {csA csB : List Char} {D : E8Data}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (h : e8K d A B D = true) : e8Check (ops2 d) D = true := by
  simp only [e8K, seedsOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, hexp, hn, hprog, hrx, hrh, hoh, hoh16, ht, hX2, hH, hv, hc2, hc3, hconj⟩ := h
  have hreg : ∀ r < D.nregs, ((ops2 d).regsOf D.seedA D.seedB D.nregs D.prog)[r]! =
      unpackR d (getR d (runK d A B D.nregs D.prog) r) :=
    fun r hr => mRegs_get hA hB hsA hsB hprog hexp hr
  unfold e8Check
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  rw [hreg _ hrx, hreg _ hrh, ← unpackR_powK (by omega : D.oh - 1 < 2 ^ 16)]
  simp only [← unpackR_mulF]
  refine ⟨hn, hprog, hrx, hrh, hoh, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← unpackR_powK (by norm_num), ← unpackR_idF_eq_one]
    exact eq_of_beq hX2
  · rw [← unpackR_powK (by omega), ← unpackR_idF_eq_one]
    exact eq_of_beq hH
  · rw [unit_eq, vmul_unpackR]
    exact vne_of_beq (vmF_lt _ _ _) (pw2_lt ht) hv
  · unfold commK at hc2
    exact eq_of_beq hc2
  · unfold commK at hc3
    exact eq_of_beq hc3
  · exact conjOK_of_conjK hconj

section FourRussians

open CFSG.Sporadic.SmallF2.Native (vecMulN mulRows idRows rowsOfPayload)
open CFSG.Sporadic.SmallF2 (toVecD toVecD_apply toVecD_zero foldl_xor_toVecD)
open CFSG.SectionRank (foldl_xor_toVecD' foldl_toVecD_of_step sum_range_blocks toVecD_frEntry
  frTable_getD testBit_byte)

private theorem toVecD_frApply_width {D d nw : Nat} (Y : Array Nat) (hY : Y.size ≤ d)
    (hd : d ≤ 32 * nw) (x : Nat) :
    toVecD D (frApply nw (frTable (4 * nw) Y) x) = toVecD D (vecMulN d Y x) := by
  set f : Nat → Fin D → ZMod 2 :=
    fun j => if x.testBit j then toVecD D (Y[j]?.getD 0) else 0 with hf
  have hentry : ∀ l b, l < nw → b < 4 →
      toVecD D ((frTable (4 * nw) Y)[256 * (4 * l + b) +
        (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256]?.getD 0) =
        ∑ i ∈ Finset.range 8, f (8 * (4 * l + b) + i) := by
    intro l b hl hb
    have hc : (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256 < 256 :=
      Nat.mod_lt _ (by norm_num)
    rw [frTable_getD _ _ (by nlinarith), toVecD_frEntry]
    have e1 : (256 * (4 * l + b) + (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256) / 256 =
        4 * l + b := by omega
    have e2 : (256 * (4 * l + b) + (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256) % 256 =
        (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256 := by omega
    rw [e1, e2]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [testBit_byte x l b i hb hi, show 32 * l + 8 * b + i = 8 * (4 * l + b) + i by ring]
  have hfold : toVecD D (frApply nw (frTable (4 * nw) Y) x) =
      ∑ l ∈ Finset.range nw, ∑ b ∈ Finset.range 4, ∑ i ∈ Finset.range 8,
        f (8 * (4 * l + b) + i) := by
    have := foldl_toVecD_of_step (d := D) (fun acc l =>
        (List.range 4).foldl (fun acc b => acc ^^^ ((frTable (4 * nw) Y)[256 * (4 * l + b) +
          (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256]?.getD 0)) acc)
      (fun l => ∑ b ∈ Finset.range 4, toVecD D ((frTable (4 * nw) Y)[256 * (4 * l + b) +
          (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256]?.getD 0))
      (fun acc l => foldl_xor_toVecD' _ 4 acc) nw 0
    refine this.trans ?_
    rw [toVecD_zero, zero_add]
    refine Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun b hb => ?_
    exact hentry l b (Finset.mem_range.1 hl) (Finset.mem_range.1 hb)
  have hblocks : ∑ l ∈ Finset.range nw, ∑ b ∈ Finset.range 4, ∑ i ∈ Finset.range 8,
      f (8 * (4 * l + b) + i) = ∑ j ∈ Finset.range (32 * nw), f j := by
    have inner : ∀ l, ∑ b ∈ Finset.range 4, ∑ i ∈ Finset.range 8, f (8 * (4 * l + b) + i) =
        ∑ i ∈ Finset.range 32, f (32 * l + i) := by
      intro l
      rw [show (32 : Nat) = 8 * 4 by norm_num, ← sum_range_blocks (fun i => f (8 * 4 * l + i)) 8 4]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
      congr 1
      ring
    rw [Finset.sum_congr rfl fun l _ => inner l, sum_range_blocks f 32 nw]
  have htail : ∑ j ∈ Finset.range (32 * nw), f j = ∑ j ∈ Finset.range d, f j := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hd
    rw [hm, Finset.sum_range_add]
    have : ∑ j ∈ Finset.range m, f (d + j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hf]
      simp only
      rw [Array.getElem?_eq_none (by omega), Option.getD_none, toVecD_zero, ite_self]
    rw [this, add_zero]
  rw [hfold, hblocks, htail]
  unfold vecMulN
  rw [foldl_xor_toVecD D (fun j => x.testBit j = true), toVecD_zero, zero_add]

private theorem frApply_eq_vecMulN {d nw : Nat} (Y : Array Nat) (hY : Y.size ≤ d)
    (hd : d ≤ 32 * nw) (x : Nat) : frApply nw (frTable (4 * nw) Y) x = vecMulN d Y x := by
  apply Nat.eq_of_testBit_eq
  intro q
  have h := congrFun (toVecD_frApply_width (D := q + 1) Y hY hd x) ⟨q, Nat.lt_succ_self q⟩
  simp only [toVecD_apply] at h
  cases h1 : (frApply nw (frTable (4 * nw) Y) x).testBit q <;>
    cases h2 : (vecMulN d Y x).testBit q <;> simp_all

private theorem frMul_eq_mulRows {d : Nat} (X Y : Array Nat) (hY : Y.size ≤ d) :
    frMul d X Y = mulRows d X Y := by
  show X.map (frApply ((d + 31) / 32) (frTable (4 * ((d + 31) / 32)) Y)) = X.map (vecMulN d Y)
  congr 1
  funext x
  exact frApply_eq_vecMulN Y hY (by omega) x

private theorem size_getElem!_le {d : Nat} {R : Array (Array Nat)} (hR : ∀ x ∈ R, x.size ≤ d)
    (r : Nat) : (R[r]!).size ≤ d := by
  by_cases h : r < R.size
  · rw [getElem!_pos R r h]
    exact hR _ (Array.getElem_mem h)
  · rw [getElem!_neg R r h]
    exact Nat.zero_le d

private theorem size_ops2_mul {d : Nat} {X Y : Array Nat} (hX : X.size ≤ d) :
    ((ops2 d).mul X Y).size ≤ d := by
  show (mulRows d X Y).size ≤ d
  rw [mulRows, Array.size_map]
  exact hX

private theorem pow_fr {d : Nat} (e : Nat) : ∀ X : Array Nat, X.size ≤ d →
    (ops2fr d).pow X e = (ops2 d).pow X e ∧ ((ops2 d).pow X e).size ≤ d := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro X hX
    have hXX : (ops2fr d).mul X X = (ops2 d).mul X X := frMul_eq_mulRows X X hX
    unfold Ops.pow
    dsimp only
    split_ifs with h0 h1 ho
    · exact ⟨rfl, by simp [ops2, idRows]⟩
    · exact ⟨rfl, hX⟩
    · obtain ⟨ihe, ihs⟩ := ih (e / 2) (by omega) ((ops2 d).mul X X) (size_ops2_mul hX)
      rw [hXX, ihe]
      exact ⟨frMul_eq_mulRows X _ ihs, size_ops2_mul hX⟩
    · obtain ⟨ihe, ihs⟩ := ih (e / 2) (by omega) ((ops2 d).mul X X) (size_ops2_mul hX)
      rw [hXX]
      exact ⟨ihe, ihs⟩

private theorem step_fr {d : Nat} (R : Array (Array Nat)) (hR : ∀ x ∈ R, x.size ≤ d) (op : Op) :
    (ops2fr d).step R op = (ops2 d).step R op ∧ ∀ x ∈ (ops2 d).step R op, x.size ≤ d := by
  have hset : ∀ (k : Nat) (v : Array Nat), v.size ≤ d → ∀ x ∈ R.set! k v, x.size ≤ d := by
    intro k v hv x hx
    rw [Array.set!_eq_setIfInBounds] at hx
    rcases Array.mem_or_eq_of_mem_setIfInBounds hx with hx | rfl
    · exact hR x hx
    · exact hv
  cases op with
  | mul i j k =>
    have e : (ops2fr d).mul R[i]! R[j]! = (ops2 d).mul R[i]! R[j]! :=
      frMul_eq_mulRows _ _ (size_getElem!_le hR j)
    refine ⟨?_, hset k ((ops2 d).mul R[i]! R[j]!) (size_ops2_mul (size_getElem!_le hR i))⟩
    show R.set! k ((ops2fr d).mul R[i]! R[j]!) = R.set! k ((ops2 d).mul R[i]! R[j]!)
    rw [e]
  | pow e i k =>
    obtain ⟨he, hs⟩ := pow_fr e R[i]! (size_getElem!_le hR i)
    refine ⟨?_, hset k ((ops2 d).pow R[i]! e) hs⟩
    show R.set! k ((ops2fr d).pow R[i]! e) = R.set! k ((ops2 d).pow R[i]! e)
    rw [he]

private theorem run_fr {d : Nat} : ∀ (prog : List Op) (R : Array (Array Nat)),
    (∀ x ∈ R, x.size ≤ d) →
      (ops2fr d).run prog R = (ops2 d).run prog R ∧ ∀ x ∈ (ops2 d).run prog R, x.size ≤ d
  | [], _, hR => ⟨rfl, hR⟩
  | op :: prog, R, hR => by
    obtain ⟨e, hs⟩ := step_fr R hR op
    obtain ⟨e', hs'⟩ := run_fr prog ((ops2 d).step R op) hs
    refine ⟨?_, hs'⟩
    show prog.foldl (ops2fr d).step ((ops2fr d).step R op) =
      prog.foldl (ops2 d).step ((ops2 d).step R op)
    rw [e]
    exact e'

private theorem regsOf_fr {d : Nat} (sA sB : String) (n : Nat) (prog : List Op) :
    (ops2fr d).regsOf sA sB n prog = (ops2 d).regsOf sA sB n prog ∧
      ∀ x ∈ (ops2 d).regsOf sA sB n prog, x.size ≤ d := by
  have hinit : ∀ x ∈ (ops2 d).initRegs ((ops2 d).decode sA) ((ops2 d).decode sB) n,
      x.size ≤ d := by
    intro x hx
    rw [Ops.initRegs, Array.mem_ofFn] at hx
    obtain ⟨r, rfl⟩ := hx
    split_ifs <;> simp [ops2, rowsOfPayload, idRows]
  exact run_fr prog _ hinit

private theorem evalW_fr {d : Nat} {R : Array (Array Nat)} (hR : ∀ x ∈ R, x.size ≤ d) :
    ∀ w : Word, evalW (ops2fr d) R w = evalW (ops2 d) R w ∧ (evalW (ops2 d) R w).size ≤ d
  | [] => ⟨rfl, by simp [evalW, ops2, idRows]⟩
  | (r, e) :: w => by
    obtain ⟨hw, hws⟩ := evalW_fr hR w
    obtain ⟨hp, hps⟩ := pow_fr e R[r]! (size_getElem!_le hR r)
    refine ⟨?_, size_ops2_mul hps⟩
    show (ops2fr d).mul ((ops2fr d).pow R[r]! e) (evalW (ops2fr d) R w) =
      (ops2 d).mul ((ops2 d).pow R[r]! e) (evalW (ops2 d) R w)
    rw [hw, hp]
    exact frMul_eq_mulRows _ _ hws

private theorem factOK_fr {d : Nat} {R : Array (Array Nat)} (hR : ∀ x ∈ R, x.size ≤ d)
    (n : Nat) : ∀ f : MFact, factOK (ops2fr d) R n f = factOK (ops2 d) R n f
  | .ord r e => by
    simp only [factOK]
    rw [(pow_fr e R[r]! (size_getElem!_le hR r)).1]
    rfl
  | .conj h u w => by
    obtain ⟨hu, hus⟩ := evalW_fr hR u
    obtain ⟨hw, -⟩ := evalW_fr hR w
    have e1 : (ops2fr d).mul R[h]! (evalW (ops2 d) R u) = (ops2 d).mul R[h]! (evalW (ops2 d) R u) :=
      frMul_eq_mulRows _ _ hus
    have e2 : (ops2fr d).mul (evalW (ops2 d) R w) R[h]! = (ops2 d).mul (evalW (ops2 d) R w) R[h]! :=
      frMul_eq_mulRows _ _ (size_getElem!_le hR h)
    simp only [factOK]
    rw [hu, hw, e1, e2]
    rfl
  | .ne w₁ w₂ t => by
    simp only [factOK]
    rw [(evalW_fr hR w₁).1, (evalW_fr hR w₂).1]
    rfl
  | .eq w₁ w₂ => by
    simp only [factOK]
    rw [(evalW_fr hR w₁).1, (evalW_fr hR w₂).1]
    rfl

end FourRussians

theorem mcertCheck_fr_of_K {d A B : Nat} {csA csB : List Char} {sA sB : String} {C : MCert}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : sA = String.ofList csA) (hsB : sB = String.ofList csB)
    (h : mcertK d A B C = true) : mcertCheck (ops2fr d) sA sB C = true := by
  obtain ⟨hregs, hR⟩ := regsOf_fr (d := d) sA sB C.nregs C.prog
  have hf : factOK (ops2fr d) ((ops2fr d).regsOf sA sB C.nregs C.prog) C.nregs =
      factOK (ops2 d) ((ops2 d).regsOf sA sB C.nregs C.prog) C.nregs := by
    rw [hregs]
    exact funext (factOK_fr hR C.nregs)
  have e : mcertCheck (ops2fr d) sA sB C = mcertCheck (ops2 d) sA sB C := by
    show (decide (2 ≤ C.nregs) && C.prog.all (Op.lt C.nregs) &&
        C.facts.all (factOK (ops2fr d) ((ops2fr d).regsOf sA sB C.nregs C.prog) C.nregs)) =
      (decide (2 ≤ C.nregs) && C.prog.all (Op.lt C.nregs) &&
        C.facts.all (factOK (ops2 d) ((ops2 d).regsOf sA sB C.nregs C.prog) C.nregs))
    rw [hf]
  rw [e]
  exact mcertCheck_of_K hA hB hsA hsB h

end CFSG.KC.OpsF2K

end
