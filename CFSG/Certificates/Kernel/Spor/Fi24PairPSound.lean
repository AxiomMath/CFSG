module

public import Certificates.Data.Kernel.Spor.Fi24PairP
public import CFSG.Certificates.Kernel.Spor.Fi24PairSound
public import CFSG.Certificates.Kernel.Spor.Fi24NetPtSound

public section

namespace CFSG.KC.Fi24PairP

open CFSG.KC.Fi24Pair CFSG.KS.Fi24Net

section Aux

open CFSG.KC CFSG.KC.Benes CFSG.KC.Loop CFSG.KC.MonsterConv.Perm CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt

private theorem natRec_add_eq_sum (F : ℕ → ℕ) : ∀ k,
    Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k =
      ∑ l ∈ Finset.range k, F l
  | 0 => by simp
  | k + 1 => by
    change F k + Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k = _
    rw [natRec_add_eq_sum F k, Finset.sum_range_succ, Nat.add_comm]

private theorem sumBelow_eq_sum64 (m : ℕ) (f : ℕ → ℕ) : ∀ hi, sumBelow m hi f =
    ∑ i ∈ Finset.range (64 * hi), Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m)
  | 0 => by simp [sumBelow]
  | hi + 1 => by
    have e : sumBelow m (hi + 1) f = Nat.add (Nat.rec (motive := fun _ => ℕ) 0
        (fun l ih2 => Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft hi 6) l)) ih2) 64) (sumBelow m hi f) := rfl
    have e2 : ∀ l, Nat.add (Nat.shiftLeft hi 6) l = 64 * hi + l := fun l => by
      change hi <<< 6 + l = _
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
    rw [e, natRec_add_eq_sum, sumBelow_eq_sum64 m f hi, Nat.mul_succ, Finset.sum_range_add]
    simp only [e2]
    exact Nat.add_comm _ _

private theorem sumBelow_eq_sum {m hi : ℕ} (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  rw [sumBelow_eq_sum64]
  obtain ⟨d, hd⟩ : ∃ d, 64 * hi = m + d := ⟨64 * hi - m, by omega⟩
  rw [hd, Finset.sum_range_add]
  have h2 : ∑ l ∈ Finset.range d,
      Bool.rec (motive := fun _ => ℕ) 0 (f (m + l)) (Nat.blt (m + l) m) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    have hb : Nat.blt (m + l) m = false := by
      cases e : Nat.blt (m + l) m
      · rfl
      · rw [Nat.blt_eq] at e
        omega
    rw [hb]
  rw [h2, Nat.add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hb : Nat.blt i m = true := Nat.blt_eq.mpr (Finset.mem_range.1 hi)
  rw [hb]

private theorem testBit_ones' (n i : ℕ) : (ones n).testBit i = decide (i < n) := by
  rw [ones_eq, Nat.testBit_two_pow_sub_one]

private theorem testBit_gath {CF : ℕ → ℕ} (hCF : NV CF) (v p : ℕ) :
    (gath CF v).testBit p = (v.testBit (pF CF p) && decide (p < 3240)) := by
  unfold gath
  rw [nland, Nat.testBit_and, testBit_netF hCF, ← testBit_ones' 3240 p]

private theorem testBit_sumBits (FP : ℕ → ℕ) (k : ℕ) : ∀ n,
    (∑ i ∈ Finset.range n, (((FP i >>> k) &&& 1) <<< i)) < 2 ^ n ∧
    ∀ p, (∑ i ∈ Finset.range n, (((FP i >>> k) &&& 1) <<< i)).testBit p =
      (decide (p < n) && (FP p).testBit k)
  | 0 => ⟨by simp, fun p => by simp⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := testBit_sumBits FP k n
    have hb1 : ((FP n >>> k) &&& 1) = 0 ∨ ((FP n >>> k) &&& 1) = 1 := by
      rw [Nat.and_one_is_mod]
      omega
    have e : ∑ i ∈ Finset.range (n + 1), (((FP i >>> k) &&& 1) <<< i) =
        2 ^ n * ((FP n >>> k) &&& 1) +
          ∑ i ∈ Finset.range n, (((FP i >>> k) &&& 1) <<< i) := by
      rw [Finset.sum_range_succ, Nat.shiftLeft_eq]
      ring
    rw [e]
    refine ⟨?_, fun p => ?_⟩
    · rcases hb1 with h | h <;> rw [h, pow_succ] <;> omega
    · rw [Nat.testBit_two_pow_mul_add _ h1 p]
      by_cases hp : p < n
      · rw [if_pos hp, h2 p, decide_eq_true hp, decide_eq_true (by omega)]
      · rw [if_neg hp]
        rcases Nat.lt_or_ge n p with hnp | hnp
        · have hz : ((FP n >>> k) &&& 1).testBit (p - n) = false := by
            apply Nat.testBit_lt_two_pow
            have : 2 ^ 1 ≤ 2 ^ (p - n) := Nat.pow_le_pow_right (by norm_num) (by omega)
            rcases hb1 with h | h <;> rw [h] <;> omega
          rw [hz, decide_eq_false (by omega)]
          simp
        · have hpn : p = n := by omega
          subst hpn
          rw [Nat.sub_self, decide_eq_true (by omega)]
          rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq (x := FP p) (i := k),
            Nat.testBit_zero, Nat.shiftRight_eq_div_pow]
          simp

private theorem testBit_fpl (FP : ℕ → ℕ) (k p : ℕ) :
    (fpl FP k).testBit p = (decide (p < 3240) && (FP p).testBit k) := by
  have e : fpl FP k = ∑ i ∈ Finset.range 3240, (((FP i >>> k) &&& 1) <<< i) :=
    sumBelow_eq_sum _ (by norm_num)
  rw [e, (testBit_sumBits FP k 3240).2]

private theorem testBit_tf (P : ℕ → ℕ) (k p : ℕ) :
    (tf P k).testBit p =
      if k = 0 then (P 0).testBit p else ((P k).testBit p ^^ (P 0).testBit p) := by
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    rfl
  · rw [if_neg hk]
    have e : tf P k = Nat.xor (P k) (P 0) := by
      unfold tf
      rw [beq_false hk]
    rw [e, nxor, Nat.testBit_xor]

private theorem testBit_pl12 (PL j p : ℕ) :
    (pl12 PL j).testBit p = (PL.testBit (4096 * j + p) && decide (p < 3240)) := by
  unfold pl12
  rw [nland, Nat.testBit_and, nshr, Nat.testBit_shiftRight, nmul, ← testBit_ones' 3240 p]

private theorem bits_of_tpl {a b : ℕ} (ha : a < 524288) (hb : b < 524288) {n : ℕ} (hn : n ≤ 19)
    (h : ∀ k < n, (tpl k).testBit a = (tpl k).testBit b) : ∀ k < n, a.testBit k = b.testBit k := by
  intro k hk
  have h0 := h 0 (by omega)
  rw [tpl_testBit (by decide) ha, tpl_testBit (by decide) hb, if_pos rfl, if_pos rfl] at h0
  by_cases k0 : k = 0
  · subst k0
    exact h0
  · have e := h k hk
    rw [tpl_testBit (by omega) ha, tpl_testBit (by omega) hb, if_neg k0, if_neg k0, h0] at e
    revert e
    cases a.testBit k <;> cases b.testBit k <;> cases b.testBit 0 <;> decide

private theorem pF_eq_FP {CF FP : ℕ → ℕ} (hCF : NV CF) (hFP : ∀ p < 3240, FP p < 524288)
    (hc : cfOK CF FP = true) : ∀ p < 3240, pF CF p = FP p := by
  intro p hp
  unfold cfOK at hc
  obtain ⟨-, hc2⟩ := andB_true hc
  have hk := recAll_left (P := fun k => Nat.beq (gath CF (tpl k)) (tf (fpl FP) k)) 19 hc2
  have hlt : pF CF p < 524288 := pF_lt hCF (by omega)
  refine eq_of_planes hlt (hFP p hp) (bits_of_tpl hlt (hFP p hp) (Nat.le_refl 19) fun k hk' => ?_)
  have e := Nat.eq_of_beq_eq_true (hk k hk')
  have e2 := congrArg (fun x => x.testBit p) e
  simp only [testBit_gath hCF, testBit_tf, testBit_fpl, decide_eq_true hp, Bool.and_true,
    Bool.true_and] at e2
  rw [e2, tpl_testBit (by omega) (hFP p hp)]

private theorem LN_lt {NW : ℕ → ℕ → ℕ} {l : ℕ} (hl : NV (NW (l / 2))) {x : ℕ} (hx : x < 524288) :
    LN NW l x < 524288 := by
  unfold LN
  split_ifs
  · exact pF_lt hl hx
  · exact pR_lt hl hx

private theorem planes_testBit {NW b p : ℕ} (hv : StagesValid 12 NW) (hb : b < 12) (hp : p < 4096) :
    (planesNW NW).testBit (4096 * b + p) = (benesPerm 12 NW p).testBit b := by
  have e := (testBit_netApply (k := 12) (W := 4096) (P := 12) (N := NW) (by norm_num) hv
    (idP 12)).1 b hb p hp
  have e2 := YModel.Sem.testBit_idP (k := 12) hb (benesPerm_lt hv hp)
  exact e.trans e2

private theorem sigP_main {NW : ℕ → ℕ → ℕ} {CF FP : ℕ → ℕ} {NS l : ℕ} (hCF : NV CF)
    (hl : NV (NW (l / 2))) (hFP : ∀ p < 3240, FP p < 524288) (hc : cfOK CF FP = true)
    (h : sigP NW CF NS l = true) : SigF (fun r => LN NW r) FP NS l := by
  have hpF := pF_eq_FP hCF hFP hc
  unfold sigP at h
  obtain ⟨h1, h2⟩ := andB_true h
  have hv : StagesValid 12 NS := stagesValid_of_netValid h1
  rw [letB_eq'] at h2
  obtain ⟨h3, h4⟩ := andB_true h2
  have hj := recAll_left (P := fun j => Nat.beq (gath CF (planeL NW l (netR CF (tpl j))))
    (tf (pl12 (planesNW NS)) j)) 12 h3
  refine ⟨hv, fun p hp => ?_⟩
  have hp4 : p < 4096 := by omega
  have hs : benesPerm 12 NS p < 4096 := benesPerm_lt hv (by omega : p < 2 ^ 12)
  have hy524 : pR CF (LN NW l (FP p)) < 524288 := pR_lt hCF (LN_lt hl (hFP p hp))
  have hbits : ∀ j < 12, (pR CF (LN NW l (FP p))).testBit j = (benesPerm 12 NS p).testBit j := by
    refine bits_of_tpl hy524 (by omega) (by norm_num) fun j hj' => ?_
    have e := Nat.eq_of_beq_eq_true (hj j hj')
    have e2 := congrArg (fun x => x.testBit p) e
    simp only [testBit_gath hCF, CFSG.KS.Fi24NetPt.testBit_planeL hl, testBit_netR hCF, hpF p hp,
      testBit_tf, testBit_pl12, decide_eq_true hp, Bool.and_true] at e2
    have e3 := planes_testBit hv (by omega : 0 < 12) hp4
    rw [e2, tpl_testBit (by omega) (by omega : benesPerm 12 NS p < 524288)]
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl, if_pos rfl]
      simpa using e3
    · rw [if_neg hj0, if_neg hj0, planes_testBit hv hj' hp4, e3]
  have hlt : pR CF (LN NW l (FP p)) < 3240 := by
    have e := congrArg (fun x => x.testBit p) (Nat.eq_of_beq_eq_true h4)
    simp only [testBit_gath hCF, CFSG.KS.Fi24NetPt.testBit_planeL hl, testBit_netR hCF, hpF p hp,
      testBit_ones', decide_eq_true hp, Bool.and_true] at e
    exact of_decide_eq_true e
  have hy : pR CF (LN NW l (FP p)) = benesPerm 12 NS p :=
    YModel.Sem.eq_of_bits (k := 12) (lt_of_lt_of_le hlt (by norm_num)) hs hbits
  have hσ : benesPerm 12 NS p < 3240 := hy ▸ hlt
  refine ⟨hσ, ?_⟩
  have e := pF_pR hCF (LN NW l (FP p))
  rw [hy] at e
  exact e.symm.trans (hpF _ hσ)

end Aux

theorem sigP_spec {NW : ℕ → ℕ → ℕ} {CF FP : ℕ → ℕ} {NS l : ℕ} (hCF : NV CF) (hl : NV (NW (l / 2)))
    (hFP : ∀ p < 3240, FP p < 524288) (hc : cfOK CF FP = true) (h : sigP NW CF NS l = true) :
    SigF (fun r => LN NW r) FP NS l :=
  sigP_main hCF hl hFP hc h

end CFSG.KC.Fi24PairP

end
