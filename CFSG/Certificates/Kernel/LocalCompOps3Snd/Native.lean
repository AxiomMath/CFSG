module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3

public section

namespace CFSG.KC.LocalComp.Ops3Snd

open CFSG.SectionRank CFSG.SectionRank.Native
open scoped Matrix

abbrev FV := CFSG.F3.Native.V

@[expose] def RowsBnd (d : ℕ) (X : Array FV) : Prop :=
  ∀ i : ℕ, X[i]!.p < 2 ^ d ∧ X[i]!.m < 2 ^ d

@[expose] def WFb (d : ℕ) (X : Array FV) : Prop :=
  X.size = d ∧ CFSG.F3.Native.RowsWF X ∧ RowsBnd d X

private theorem wfb_default_lt (d : ℕ) :
    (default : CFSG.F3.Native.V).p < 2 ^ d ∧ (default : CFSG.F3.Native.V).m < 2 ^ d :=
  ⟨Nat.two_pow_pos d, Nat.two_pow_pos d⟩

private theorem wfb_add_lt {d : ℕ} {a b : CFSG.F3.Native.V}
    (ha : a.p < 2 ^ d ∧ a.m < 2 ^ d) (hb : b.p < 2 ^ d ∧ b.m < 2 ^ d) :
    (CFSG.F3.Native.V.add a b).p < 2 ^ d ∧ (CFSG.F3.Native.V.add a b).m < 2 ^ d := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hb0 : b.p ||| b.m < 2 ^ d := Nat.or_lt_two_pow hb1 hb2
  have ha0 : a.p ||| a.m < 2 ^ d := Nat.or_lt_two_pow ha1 ha2
  have hP : (a.p ^^^ (a.p &&& (b.p ||| b.m))) ||| (b.p ^^^ (b.p &&& (a.p ||| a.m)))
      ||| (a.m &&& b.m) < 2 ^ d :=
    Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.xor_lt_two_pow ha1 (Nat.and_lt_two_pow _ hb0))
      (Nat.xor_lt_two_pow hb1 (Nat.and_lt_two_pow _ ha0))) (Nat.and_lt_two_pow _ hb2)
  have hM : (a.m ^^^ (a.m &&& (b.p ||| b.m))) ||| (b.m ^^^ (b.m &&& (a.p ||| a.m)))
      ||| (a.p &&& b.p) < 2 ^ d :=
    Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.xor_lt_two_pow ha2 (Nat.and_lt_two_pow _ hb0))
      (Nat.xor_lt_two_pow hb2 (Nat.and_lt_two_pow _ ha0))) (Nat.and_lt_two_pow _ hb1)
  exact ⟨hP, hM⟩

private theorem wfb_sub_lt {d : ℕ} {a b : CFSG.F3.Native.V}
    (ha : a.p < 2 ^ d ∧ a.m < 2 ^ d) (hb : b.p < 2 ^ d ∧ b.m < 2 ^ d) :
    (CFSG.F3.Native.V.sub a b).p < 2 ^ d ∧ (CFSG.F3.Native.V.sub a b).m < 2 ^ d :=
  wfb_add_lt (b := CFSG.F3.Native.V.neg b) ha ⟨hb.2, hb.1⟩

private theorem wfb_combStep_lt {d : ℕ} (Y : Array CFSG.F3.Native.V) (r : CFSG.F3.Native.V)
    (j : ℕ) (hY : ∀ k : ℕ, Y[k]!.p < 2 ^ d ∧ Y[k]!.m < 2 ^ d) {acc : CFSG.F3.Native.V}
    (hacc : acc.p < 2 ^ d ∧ acc.m < 2 ^ d) :
    (CFSG.F3.Native.combStep Y r j acc).p < 2 ^ d ∧
      (CFSG.F3.Native.combStep Y r j acc).m < 2 ^ d := by
  unfold CFSG.F3.Native.combStep
  split_ifs
  · exact wfb_add_lt hacc (hY j)
  · exact wfb_sub_lt hacc (hY j)
  · exact hacc

private theorem wfb_fold_combStep_lt (d : ℕ) (Y : Array CFSG.F3.Native.V)
    (r : CFSG.F3.Native.V) (hY : ∀ k : ℕ, Y[k]!.p < 2 ^ d ∧ Y[k]!.m < 2 ^ d) (n : ℕ) :
    (Nat.fold n (fun j _ acc => CFSG.F3.Native.combStep Y r j acc)
        CFSG.F3.Native.V.zero).p < 2 ^ d ∧
      (Nat.fold n (fun j _ acc => CFSG.F3.Native.combStep Y r j acc)
        CFSG.F3.Native.V.zero).m < 2 ^ d := by
  induction n with
  | zero => rw [Nat.fold_zero]; exact ⟨Nat.two_pow_pos d, Nat.two_pow_pos d⟩
  | succ n ih =>
    rw [Nat.fold_succ]
    exact wfb_combStep_lt Y r n hY ih

private theorem wfb_comb_lt (d : ℕ) (Y : Array CFSG.F3.Native.V) (r : CFSG.F3.Native.V)
    (hY : ∀ k : ℕ, Y[k]!.p < 2 ^ d ∧ Y[k]!.m < 2 ^ d) :
    (CFSG.F3.Native.comb d Y r).p < 2 ^ d ∧ (CFSG.F3.Native.comb d Y r).m < 2 ^ d := by
  rw [CFSG.F3.Native.comb_eq_fold]
  exact wfb_fold_combStep_lt d Y r hY d

private theorem wfb_ofFn_p_lt (d : ℕ) (f : ℕ → ℕ) :
    (CFSG.F3.Native.V.ofFn d f).p < 2 ^ d := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hnot : ¬ i < d := by omega
  rw [CFSG.F3.Native.ofFn_eq_fold, (CFSG.F3.Native.fold_ofFnStep_bits f i d).1,
    decide_eq_false hnot, Bool.false_and]

private theorem wfb_ofFn_m_lt (d : ℕ) (f : ℕ → ℕ) :
    (CFSG.F3.Native.V.ofFn d f).m < 2 ^ d := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hnot : ¬ i < d := by omega
  rw [CFSG.F3.Native.ofFn_eq_fold, (CFSG.F3.Native.fold_ofFnStep_bits f i d).2,
    decide_eq_false hnot, Bool.false_and]

theorem wfb_rowsOf (d : ℕ) (s : String) : WFb d (CFSG.F3.Native.rowsOf d s) := by
  unfold WFb RowsBnd
  refine ⟨?_, CFSG.F3.Native.RowsWF.rowsOf d s, fun i => ?_⟩
  · simp [CFSG.F3.Native.rowsOf]
  · by_cases hi : i < d
    · unfold CFSG.F3.Native.rowsOf
      rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
      exact ⟨wfb_ofFn_p_lt _ _, wfb_ofFn_m_lt _ _⟩
    · unfold CFSG.F3.Native.rowsOf
      rw [getElem!_neg _ i (by simpa using hi)]
      exact wfb_default_lt d

theorem wfb_idM (d : ℕ) : WFb d (CFSG.F3.Native.idM d) := by
  unfold WFb RowsBnd
  refine ⟨?_, CFSG.F3.Native.RowsWF.idM d, fun i => ?_⟩
  · simp [CFSG.F3.Native.idM]
  · by_cases hi : i < d
    · unfold CFSG.F3.Native.idM
      rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
      refine ⟨?_, ?_⟩
      · show 1 <<< i < 2 ^ d
        rw [Nat.one_shiftLeft]
        exact Nat.pow_lt_pow_right (by norm_num) hi
      · show 0 < 2 ^ d
        exact Nat.two_pow_pos d
    · unfold CFSG.F3.Native.idM
      rw [getElem!_neg _ i (by simpa using hi)]
      exact wfb_default_lt d

theorem wfb_mul {d : ℕ} {X Y : Array FV} (hX : WFb d X) (hY : WFb d Y) :
    WFb d (CFSG.F3.Native.mul d X Y) := by
  unfold WFb at hX hY ⊢
  obtain ⟨hXs, hXw, hXb⟩ := hX
  obtain ⟨hYs, hYw, hYb⟩ := hY
  unfold RowsBnd at hXb hYb ⊢
  have hsz : (CFSG.F3.Native.mul d X Y).size = d := by
    unfold CFSG.F3.Native.mul
    rw [Array.size_map, hXs]
  refine ⟨hsz, CFSG.F3.Native.RowsWF.mul X d hXw hYw, fun i => ?_⟩
  by_cases hi : i < X.size
  · rw [CFSG.F3.Native.mul_getElem! hi]
    exact wfb_comb_lt d Y X[i]! hYb
  · rw [getElem!_neg _ i (by omega)]
    exact wfb_default_lt d

private theorem natB_bitVal_inj :
    ∀ p m p' m' : Bool, (p && m) = false → (p' && m') = false →
      CFSG.F3.Native.bitVal p m = CFSG.F3.Native.bitVal p' m' → p = p' ∧ m = m' := by
  decide

private theorem natB_beq_of_val_below {d : ℕ} {a b : CFSG.F3.Native.V} (ha : a.wf = true)
    (hb : b.wf = true) (hpa : a.p < 2 ^ d) (hma : a.m < 2 ^ d) (hpb : b.p < 2 ^ d)
    (hmb : b.m < 2 ^ d)
    (h : ∀ j : ℕ, j < d → CFSG.F3.Native.V.val a j = CFSG.F3.Native.V.val b j) :
    CFSG.F3.Native.V.beq a b = true := by
  have key : ∀ j : ℕ, a.p.testBit j = b.p.testBit j ∧ a.m.testBit j = b.m.testBit j := by
    intro j
    by_cases hj : j < d
    · have hv := h j hj
      rw [CFSG.F3.Native.V.val_eq_bitVal, CFSG.F3.Native.V.val_eq_bitVal] at hv
      exact natB_bitVal_inj _ _ _ _ (CFSG.F3.Native.V.not_both ha j)
        (CFSG.F3.Native.V.not_both hb j) hv
    · have h2j : 2 ^ d ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e1 : a.p.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hpa h2j)
      have e2 : a.m.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hma h2j)
      have e3 : b.p.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hpb h2j)
      have e4 : b.m.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hmb h2j)
      exact ⟨by rw [e1, e3], by rw [e2, e4]⟩
  rw [CFSG.F3.Native.V.beq_iff]
  exact ⟨Nat.eq_of_testBit_eq fun j => (key j).1, Nat.eq_of_testBit_eq fun j => (key j).2⟩

theorem eqM_of_toMat_eq {d : ℕ} {X Y : Array FV} (hX : WFb d X) (hY : WFb d Y)
    (h : CFSG.F3.Native.toMat d X = CFSG.F3.Native.toMat d Y) :
    CFSG.F3.Native.eqM d X Y = true := by
  unfold CFSG.F3.Native.eqM
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hX.1, hY.1⟩, ?_⟩
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro i _
  apply natB_beq_of_val_below (hX.2.1 i.val) (hY.2.1 i.val) (hX.2.2 i.val).1 (hX.2.2 i.val).2
    (hY.2.2 i.val).1 (hY.2.2 i.val).2
  intro j hj
  have e : CFSG.F3.Native.toMat d X i ⟨j, hj⟩ = CFSG.F3.Native.toMat d Y i ⟨j, hj⟩ := by
    rw [h]
  rw [CFSG.F3.Native.toMat_apply, CFSG.F3.Native.toMat_apply] at e
  exact e

@[expose] noncomputable def spec3b (d : ℕ) : OpsSpec (ops3 d) 3 d where
  toMat := CFSG.F3.Native.toMat d
  toVec v j := v.val j.val
  WF := WFb d
  VWF v := v.wf = true
  decode_wf s := wfb_rowsOf d s
  toMat_decode s := (spec3 d).toMat_decode s
  mul_wf hX hY := wfb_mul hX hY
  toMat_mul hX hY := (spec3 d).toMat_mul ⟨hX.1, hX.2.1⟩ ⟨hY.1, hY.2.1⟩
  one_wf := wfb_idM d
  toMat_one := (spec3 d).toMat_one
  toMat_eq _ _ h := CFSG.F3.Native.toMat_eq_of_eqM h
  vmul_wf hv hX := (spec3 d).vmul_wf hv ⟨hX.1, hX.2.1⟩
  toVec_vmul hv hX := (spec3 d).toVec_vmul hv ⟨hX.1, hX.2.1⟩
  unit_wf k := (spec3 d).unit_wf k
  toVec_ne := (spec3 d).toVec_ne

theorem vne_of_toVec_ne {d : ℕ} {u w : FV} (h : (spec3b d).toVec u ≠ (spec3b d).toVec w) :
    (ops3 d).vne u w = true := by
  obtain ⟨j, hj⟩ : ∃ j : Fin d, CFSG.F3.Native.V.val u j.val ≠ CFSG.F3.Native.V.val w j.val := by
    by_contra hc
    apply h
    funext j
    by_contra hj
    exact hc ⟨j, hj⟩
  show (List.range d).any (fun j => CFSG.F3.Native.V.get u j != CFSG.F3.Native.V.get w j) = true
  rw [List.any_eq_true]
  refine ⟨j.val, List.mem_range.2 j.isLt, ?_⟩
  show (CFSG.F3.Native.V.get u j.val != CFSG.F3.Native.V.get w j.val) = true
  rw [bne_iff_ne]
  intro he
  apply hj
  show ((CFSG.F3.Native.V.get u j.val : ℕ) : ZMod 3) = ((CFSG.F3.Native.V.get w j.val : ℕ) : ZMod 3)
  rw [he]

theorem toVec_unit (d k : ℕ) :
    (spec3b d).toVec ((ops3 d).unit k) = fun j : Fin d => if (j : ℕ) = k then (1 : ZMod 3) else 0 := by
  funext j
  show CFSG.F3.Native.V.val (⟨1 <<< k, 0⟩ : CFSG.F3.Native.V) j.val = _
  rw [CFSG.F3.Native.V.val_eq_bitVal]
  dsimp only
  rw [CFSG.F3.Native.testBit_one_shiftLeft, Nat.zero_testBit]
  by_cases h : (j : ℕ) = k <;> simp [h, CFSG.F3.Native.bitVal]


end CFSG.KC.LocalComp.Ops3Snd

end
