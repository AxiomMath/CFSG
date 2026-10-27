module

public import Certificates.Data.Kernel.SmithD6.StabTreeK
public import CFSG.Certificates.Kernel.KeyTreeChunksSound
public import CFSG.Certificates.Kernel.PkTreeSound

public section

namespace CFSG.KD.SmithD6ST

open CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6Nc

theorem beqN (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, beq_iff_eq])

theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = (if c = true then t else e) := by
  cases c <;> rfl

theorem parB_eq (x : Nat) : parB x = par6K x := beqN _ _

theorem bfB_eq (x y : Nat) : bfB x y = bfK x y := by
  have h : ∀ a b : Bool, bIf(a, bIf(b, false, true), b) = (a ^^ b) := by decide
  have e : bfB x y = (parB (Nat.land (Nat.land x 63) (Nat.shiftRight y 6)) ^^
      parB (Nat.land (Nat.land y 63) (Nat.shiftRight x 6))) := h _ _
  rw [e, parB_eq, parB_eq]
  rfl

theorem sglN_eq (u w x : Nat) : sglN u w x = sglK u w x := by
  unfold sglN sglK
  rw [bfB_eq, bfB_eq, nIf_eq, nIf_eq]
  rfl

theorem minN_eq (a b : Nat) : minN a b = min a b := by
  unfold minN
  rw [Nat.min_def]
  by_cases h : a ≤ b
  · have hb : Nat.ble a b = true := by rw [Nat.ble_eq]; exact h
    rw [if_pos h, hb]
  · have hb : Nat.ble a b = false := by
      cases e : Nat.ble a b
      · rfl
      · rw [Nat.ble_eq] at e
        exact absurd e h
    rw [if_neg h, hb]

theorem maxN_eq (a b : Nat) : maxN a b = max a b := by
  unfold maxN
  rw [Nat.max_def]
  by_cases h : a ≤ b
  · have hb : Nat.ble a b = true := by rw [Nat.ble_eq]; exact h
    rw [if_pos h, hb]
  · have hb : Nat.ble a b = false := by
      cases e : Nat.ble a b
      · rfl
      · rw [Nat.ble_eq] at e
        exact absurd e h
    rw [if_neg h, hb]

theorem key2N_eq (x1 x2 : Nat) : key2N x1 x2 = key3 x1 x2 (x1 ^^^ x2) := by
  unfold key2N keyLH
  rw [minN_eq, minN_eq, maxN_eq, maxN_eq]
  rfl

theorem imgN_eq (a b : Nat) : imgN a b = imgKey a b := by
  unfold imgN img4N
  rw [sglN_eq, sglN_eq, key2N_eq]
  rfl

theorem imgEqN_sound {a b k : Nat} (h : imgEqN a b k = true) (hk : lineTree.memB k = true) :
    imgOK a b = true ∧ imgKey a b = k := by
  unfold imgEqN eq4N eq2N eqLH at h
  rw [sglN_eq, sglN_eq, minN_eq, minN_eq, maxN_eq, maxN_eq] at h
  obtain ⟨h1, h⟩ := pkAnd_true h
  obtain ⟨h2, h3⟩ := pkAnd_true h
  have h1' := Nat.le_of_ble_eq_true h1
  have h2' := Nat.le_of_ble_eq_true h2
  have h3' := Nat.eq_of_beq_eq_true h3
  unfold keyLH at h3'
  refine ⟨?_, ?_⟩
  · simp only [imgOK, key3OK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨h1', h2'⟩, ?_⟩
    rw [← hk]
    exact congrArg (fun z => KT.memB z lineTree) h3'
  · exact h3'

theorem len_filter3 (f : Nat → Bool) (a b c : Nat) :
    ([a, b, c].filter f).length =
      (if f a = true then 1 else 0) + (if f b = true then 1 else 0) +
        (if f c = true then 1 else 0) := by
  simp only [List.filter_cons, List.filter_nil]
  cases f a <;> cases f b <;> cases f c <;> rfl

theorem inN_eq (t u w x : Nat) :
    inN t u w x = if [u, w, x].contains t = true then 1 else 0 := by
  unfold inN
  rw [nIf_eq, nIf_eq, nIf_eq, beqN, beqN, beqN]
  by_cases h1 : t = u <;> by_cases h2 : t = w <;> by_cases h3 : t = x <;> simp [h1, h2, h3]

theorem meetN_eq (u w : Nat) : meetN u w (Nat.xor u w) = meetP (1, 2) (u, w) := by
  unfold meetN meetP
  rw [len_filter3, inN_eq, inN_eq, inN_eq]
  rfl

theorem rowN_eq (b1 b2 : Bool) : rowN b1 b2 = b1.toNat + 2 * b2.toNat := by
  cases b1 <;> cases b2 <;> rfl

theorem rankR_eq (r0 r1 : Nat) : rankR r0 r1 =
    if (r0 == 0 && r1 == 0) = true then 0 else
      if (r0 == 0 || r1 == 0 || r0 == r1) = true then 1 else 2 := by
  unfold rankR
  rw [nIf_eq, nIf_eq, beqN, beqN, beqN]
  cases (r0 == 0) <;> cases (r1 == 0) <;> cases (r0 == r1) <;> rfl

theorem clsMR_eq (m r : Nat) : clsMR m r =
    if (m == 1) = true then (if (r == 0) = true then 1 else 2)
    else if (r == 0) = true then 3 else if (r == 1) = true then 4 else 5 := by
  unfold clsMR
  simp only [nIf_eq, beqN]

theorem clsN_eq (k : Nat) : clsN k = clsK k := by
  unfold clsN clsK clsP
  rw [nIf_eq, beqN]
  by_cases hk : (k == 4098) = true
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk]
    unfold clsUW
    rw [clsMR_eq, meetN_eq, rowN_eq, rowN_eq, rankR_eq, bfB_eq, bfB_eq, bfB_eq, bfB_eq]
    rfl

theorem stTreeGo_sound : ∀ (l : List Nat) (i : Nat), stTreeGo l i = true →
    ∀ j < l.length, stRecGo (l.getD j 0) (pkGet JST.stD 4 (i + j)) (pkGet JST.stG 6 (i + j)) = true
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | k :: l, i, h, j, hj => by
    have e : stTreeGo (k :: l) i =
        bAnd(stRecGo k (pkGet JST.stD 4 i) (pkGet JST.stG 6 i), stTreeGo l (i + 1)) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_true h
    rcases j with _ | j
    · simpa using h1
    · have := stTreeGo_sound l (i + 1) h2 j (by simpa using hj)
      rw [List.getD_cons_succ, show i + (j + 1) = i + 1 + j by omega]
      exact this

theorem stRecGo_sound {k d g : Nat} (h : stRecGo k d g = true) :
    0 < d ∧ (d = 1 → k = repKeys.getD (clsK k) 0) ∧
    (d ≠ 1 → g < 42 ∧ ∃ p, KT.find (imgKey (stKeysL.getD g 0) k) lineTree = p + 1 ∧
      0 < pkGet JST.stD 4 p ∧ pkGet JST.stD 4 p < d ∧
      imgEqN (stKeysL.getD g 0) (imgKey (stKeysL.getD g 0) k) k = true ∧
      clsK (imgKey (stKeysL.getD g 0) k) = clsK k) := by
  unfold stRecGo at h
  rw [imgN_eq, clsN_eq] at h
  obtain ⟨h0, h⟩ := pkAnd_true h
  refine ⟨Nat.le_of_ble_eq_true h0, fun hd => ?_, fun hd => ?_⟩
  · have hb : Nat.beq d 1 = true := by rw [hd]; rfl
    exact Nat.eq_of_beq_eq_true (pkIf_true h hb)
  · have hb : Nat.beq d 1 = false := by
      cases hb : Nat.beq d 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hd
    obtain ⟨hg, h⟩ := pkAnd_true (pkIf_false h hb)
    unfold stStepOK stParOK at h
    rw [clsN_eq, clsN_eq] at h
    obtain ⟨hp, h⟩ := pkAnd_true h
    obtain ⟨hf, hp⟩ := pkAnd_true hp
    obtain ⟨hp1, hp2⟩ := pkAnd_true hp
    obtain ⟨hi, hc⟩ := pkAnd_true h
    refine ⟨Nat.le_of_ble_eq_true hg, Nat.pred (KT.find (imgKey (stKeysL.getD g 0) k) lineTree),
      (Nat.succ_pred_eq_of_pos (Nat.le_of_ble_eq_true hf)).symm, Nat.le_of_ble_eq_true hp1,
      Nat.le_of_ble_eq_true hp2, hi, Nat.eq_of_beq_eq_true hc⟩

end CFSG.KD.SmithD6ST

end
