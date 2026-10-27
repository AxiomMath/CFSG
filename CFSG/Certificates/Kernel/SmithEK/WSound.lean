module

public import Certificates.Data.Kernel.SmithEKW
public import CFSG.Certificates.Kernel.SmithL6KSound

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE
open CFSG.SmithL6.K (maskOf maskOf_testBit lastIdx foldl_set_get lastIdx_last)
open CFSG.SmithL6.Kernel (ofFn_get! get0)

theorem getD_zero (l : List Nat) : l.getD 0 0 = l.headD 0 := by
  cases l <;> rfl

theorem getD_succ (l : List Nat) (r : Nat) : l.getD (r + 1) 0 = l.tail.getD r 0 := by
  cases l <;> simp

theorem getD_drop (l : List Nat) (a r : Nat) : (l.drop a).getD r 0 = l.getD (a + r) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_drop_take (l : List Nat) {a n r : Nat} (hr : r < n) :
    ((l.drop a).take n).getD r 0 = l.getD (a + r) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, hr]

theorem getD_mem {l : List Nat} {r : Nat} (hr : r < l.length) : l.getD r 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  exact List.getElem_mem hr

theorem foldl_ext_mem {f g : Nat → Nat → Nat} :
    ∀ (l : List Nat), (∀ a, ∀ d ∈ l, f a d = g a d) → ∀ a, l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | d :: l, h, a => by
    rw [List.foldl_cons, List.foldl_cons, h a d (List.mem_cons_self ..)]
    exact foldl_ext_mem l (fun a d hd => h a d (List.mem_cons_of_mem _ hd)) _

theorem mulsC_getD (c : Nat) {a : Nat} (ha : a < 4) : (mulsC c).getD a 0 = scaleC a c := by
  simp [mulsC, List.getD_eq_getElem?_getD, ha]

theorem vecMask_eq (W : Nat × Nat × Nat) :
    vecMask W = vecMaskK (mulsC W.1) (mulsC W.2.1) (mulsC W.2.2) := by
  unfold vecMask vecMaskK
  refine foldl_ext_mem _ (fun a d hd => ?_) 0
  have hd' := List.mem_range.mp hd
  rw [mulsC_getD _ (Nat.mod_lt _ (by omega)), mulsC_getD _ (Nat.mod_lt _ (by omega)),
    mulsC_getD _ (by omega)]

theorem wB_eq (i : Nat) : wB i = decW wData[i]! := rfl

theorem modelOK_eq (i : Nat) : modelOK i = modelOKW (wB i) (wMask i) := rfl

theorem pinsK_cons (x : Nat) (D W M : List Nat) :
    pinsK (x :: D) W M = (pinRow (decW x) (W.headD 0) (M.headD 0) && pinsK D W.tail M.tail) := rfl

theorem pinsK_sound : ∀ (D W M : List Nat), pinsK D W M = true →
    ∀ r < D.length, pinRow (decW (D.getD r 0)) (W.getD r 0) (M.getD r 0) = true
  | [], _, _, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | x :: D, W, M, h, r, hr => by
    rw [pinsK_cons, Bool.and_eq_true] at h
    cases r with
    | zero => rw [getD_zero, getD_zero, getD_zero]; exact h.1
    | succ r =>
      rw [getD_succ, getD_succ W, getD_succ M]
      exact pinsK_sound D W.tail M.tail h.2 r (by simp at hr; omega)

theorem pinChunkK_sound {D W M : List Nat} {a n : Nat} (h : pinChunkK D W M a n = true) {r : Nat}
    (hr : r < n) (hl : a + r < D.length) :
    pinRow (decW (D.getD (a + r) 0)) (W.getD (a + r) 0) (M.getD (a + r) 0) = true := by
  have e := pinsK_sound _ _ _ h r (by simp; omega)
  rwa [getD_drop_take _ hr, getD_drop_take _ hr, getD_drop_take _ hr] at e

theorem nodupK_cons (w : Nat) (l : List Nat) (S : Nat) :
    nodupK (w :: l) S = (!S.testBit w && nodupK l (S ||| 2 ^ w)) := rfl

theorem nodupK_sound : ∀ (l : List Nat) (S : Nat), nodupK l S = true →
    l.Nodup ∧ ∀ w ∈ l, S.testBit w = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | w :: l, S, h => by
    rw [nodupK_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hnd, hS⟩ := nodupK_sound l _ h.2
    have hx : ∀ x ∈ l, x ≠ w ∧ S.testBit x = false := fun x hx => by
      have e := hS x hx
      rw [Nat.testBit_or, Bool.or_eq_false_iff, Nat.testBit_two_pow] at e
      exact ⟨fun h' => by simp [h'] at e, e.1⟩
    refine ⟨List.nodup_cons.mpr ⟨fun hw => (hx w hw).1 rfl, hnd⟩, fun x hm => ?_⟩
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h.1
    · exact (hx x hm).2

theorem wBits_testBit (W : List Nat) (v : Nat) : (wBits W).testBit v = W.contains v := by
  unfold wBits maskOf
  rw [maskOf_testBit, Nat.zero_testBit, Bool.false_or]

theorem wListOK_sound {W : List Nat} (h : wListOK W = true) :
    (∀ w ∈ W, w ≠ 0 ∧ w < 2 ^ 20) ∧ W.Nodup := by
  unfold wListOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun w hw => ?_, (nodupK_sound W 0 h.2).1⟩
  have e := h.1 w hw
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at e
  exact e

theorem rowK_cons (B wi mi wj : Nat) (W M : List Nat) (f : Bool) :
    rowK B wi mi (wj :: W) M f = cond (B.testBit (wi ^^^ wj))
      (atLeast 16 (mi &&& M.headD 0) && rowK B wi mi W M.tail (wj != wi || f))
      (rowK B wi mi W M.tail f) := rfl

theorem rowK_sound {B wi mi : Nat} : ∀ (W M : List Nat) (f : Bool), rowK B wi mi W M f = true →
    (∀ s < W.length, B.testBit (wi ^^^ W.getD s 0) = true →
      atLeast 16 (mi &&& M.getD s 0) = true) ∧
    (f = true ∨ ∃ s < W.length, atLeast 16 (mi &&& M.getD s 0) = true ∧ W.getD s 0 ≠ wi)
  | [], _, _, h => ⟨fun s hs => absurd hs (Nat.not_lt_zero s), Or.inl h⟩
  | wj :: W, M, f, h => by
    rw [rowK_cons] at h
    cases hb : B.testBit (wi ^^^ wj) with
    | true =>
      rw [hb, cond_true, Bool.and_eq_true] at h
      obtain ⟨hP, hQ⟩ := rowK_sound W M.tail _ h.2
      refine ⟨fun s hs ht => ?_, ?_⟩
      · cases s with
        | zero => rw [getD_zero]; exact h.1
        | succ s =>
          rw [getD_succ] at ht ⊢
          exact hP s (by simp at hs; omega) ht
      · rcases hQ with hQ | ⟨s, hs, ha, hne⟩
        · rw [Bool.or_eq_true, bne_iff_ne] at hQ
          rcases hQ with hQ | hQ
          · exact Or.inr ⟨0, by simp, by rw [getD_zero]; exact h.1, hQ⟩
          · exact Or.inl hQ
        · refine Or.inr ⟨s + 1, by simp; omega, ?_, ?_⟩
          · rw [getD_succ]; exact ha
          · rw [getD_succ]; exact hne
    | false =>
      rw [hb, cond_false] at h
      obtain ⟨hP, hQ⟩ := rowK_sound W M.tail _ h
      refine ⟨fun s hs ht => ?_, ?_⟩
      · cases s with
        | zero => rw [getD_zero] at ht; simp at ht; rw [hb] at ht; exact absurd ht Bool.false_ne_true
        | succ s =>
          rw [getD_succ] at ht ⊢
          exact hP s (by simp at hs; omega) ht
      · rcases hQ with hQ | ⟨s, hs, ha, hne⟩
        · exact Or.inl hQ
        · refine Or.inr ⟨s + 1, by simp; omega, ?_, ?_⟩
          · rw [getD_succ]; exact ha
          · rw [getD_succ]; exact hne

theorem anyK_cons (B wi mi wj : Nat) (W M : List Nat) :
    anyK B wi mi (wj :: W) M =
      ((B.testBit (wi ^^^ wj) && atLeast 16 (mi &&& M.headD 0) && wj != wi) ||
        anyK B wi mi W M.tail) := rfl

theorem anyK_sound {B wi mi : Nat} : ∀ (W M : List Nat), anyK B wi mi W M = true →
    ∃ s < W.length, atLeast 16 (mi &&& M.getD s 0) = true ∧ W.getD s 0 ≠ wi
  | [], _, h => absurd h Bool.false_ne_true
  | wj :: W, M, h => by
    rw [anyK_cons, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne] at h
    rcases h with ⟨⟨-, ha⟩, hne⟩ | h
    · exact ⟨0, by simp, by rw [getD_zero]; exact ha, hne⟩
    · obtain ⟨s, hs, ha, hne⟩ := anyK_sound W M.tail h
      refine ⟨s + 1, by simp; omega, ?_, ?_⟩
      · rw [getD_succ]; exact ha
      · rw [getD_succ]; exact hne

theorem rowsK_cons (B : Nat) (W M : List Nat) (wi : Nat) (R S Wt Mt : List Nat) :
    rowsK B W M (wi :: R) S Wt Mt = (rowK B wi (S.headD 0) Wt Mt (anyK B wi (S.headD 0) W M) &&
      rowsK B W M R S.tail Wt.tail Mt.tail) := rfl

theorem rowsK_sound {B : Nat} {W M : List Nat} : ∀ (R S Wt Mt : List Nat),
    rowsK B W M R S Wt Mt = true → ∀ r < R.length,
      rowK B (R.getD r 0) (S.getD r 0) (Wt.drop r) (Mt.drop r)
        (anyK B (R.getD r 0) (S.getD r 0) W M) = true
  | [], _, _, _, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | wi :: R, S, Wt, Mt, h, r, hr => by
    rw [rowsK_cons, Bool.and_eq_true] at h
    cases r with
    | zero => rw [getD_zero, getD_zero, List.drop_zero, List.drop_zero]; exact h.1
    | succ r =>
      rw [getD_succ, getD_succ S, ← List.drop_tail, ← List.drop_tail]
      exact rowsK_sound R S.tail Wt.tail Mt.tail h.2 r (by simp at hr; omega)

theorem chunkK_sound {W M : List Nat} {a n : Nat} (h : chunkK W M a n = true) {r : Nat}
    (hr : r < n) (hl : a + r < W.length) :
    rowK (wBits W) (W.getD (a + r) 0) (M.getD (a + r) 0) (W.drop (a + r + 1))
      (M.drop (a + r + 1)) (anyK (wBits W) (W.getD (a + r) 0) (M.getD (a + r) 0) W M) = true := by
  have e := rowsK_sound _ _ _ _ h r (by simp; omega)
  rwa [getD_drop_take _ hr, getD_drop_take _ hr, List.drop_drop, List.drop_drop,
    Nat.add_right_comm a 1 r] at e

theorem wtArr_get {i : Nat} (hi : i < 891) : wtArr[i]! = wt i := by
  unfold wtArr
  exact ofFn_get! _ hi

theorem maskArr_get {i : Nat} (hi : i < 891) : maskArr[i]! = wMask i := by
  unfold maskArr
  exact ofFn_get! _ hi

theorem wtIdx_get {x : Nat} (hx : x < 2 ^ 20) :
    wtIdx[x]! = lastIdx (fun j => wtArr[j]!) x 891 891 := by
  unfold wtIdx
  exact foldl_set_get (fun j => wtArr[j]!) (2 ^ 20) 891 891 x hx

theorem chkW_of {W M : List Nat} (hlen : W.length = 891) (hok : wListOK W = true)
    (hpin : ∀ i < 891, pinRow (decW (wData.toList.getD i 0)) (W.getD i 0) (M.getD i 0) = true)
    (hrow : ∀ i < 891, rowK (wBits W) (W.getD i 0) (M.getD i 0) (W.drop (i + 1))
      (M.drop (i + 1)) (anyK (wBits W) (W.getD i 0) (M.getD i 0) W M) = true) :
    chkW = true := by
  obtain ⟨hall, hnd⟩ := wListOK_sound hok
  have hpin' : ∀ i < 891, wt i = W.getD i 0 ∧ wMask i = M.getD i 0 ∧ modelOK i = true := by
    intro i hi
    have e := hpin i hi
    unfold pinRow at e
    simp only [Bool.and_eq_true, beq_iff_eq] at e
    obtain ⟨⟨e1, e2⟩, e3⟩ := e
    have hw : wB i = decW (wData.toList.getD i 0) := by rw [wB_eq, get0]
    have hm : wMask i = M.getD i 0 := by
      unfold wMask
      rw [vecMask_eq, hw, e2]
    refine ⟨?_, hm, ?_⟩
    · unfold wt
      rw [hw, e1]
    · rw [modelOK_eq, hm, hw, e3]
  have hwt : ∀ i < 891, wtArr[i]! = W.getD i 0 := fun i hi => by
    rw [wtArr_get hi, (hpin' i hi).1]
  have hmk : ∀ i < 891, maskArr[i]! = M.getD i 0 := fun i hi => by
    rw [maskArr_get hi, (hpin' i hi).2.1]
  have hinj : ∀ a b, a < 891 → b < 891 → W.getD a 0 = W.getD b 0 → a = b := by
    intro a b ha hb he
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at he
    have hp := List.pairwise_iff_getElem.mp hnd
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · exact absurd he (hp a b (by omega) (by omega) hab)
    · exact hab
    · exact absurd he.symm (hp b a (by omega) (by omega) hab)
  have hmem : ∀ i < 891, W.getD i 0 ∈ W := fun i hi => getD_mem (by omega)
  have hpair : ∀ i < 891, ∀ j < 891, (wBits W).testBit (W.getD i 0 ^^^ W.getD j 0) = true →
      atLeast 16 (M.getD i 0 &&& M.getD j 0) = true := by
    have h1 : ∀ i < 891, ∀ j < 891, i < j →
        (wBits W).testBit (W.getD i 0 ^^^ W.getD j 0) = true →
        atLeast 16 (M.getD i 0 &&& M.getD j 0) = true := by
      intro i hi j hj hij ht
      have e := (rowK_sound _ _ _ (hrow i hi)).1 (j - (i + 1)) (by simp; omega)
      rw [getD_drop, getD_drop, show i + 1 + (j - (i + 1)) = j by omega] at e
      exact e ht
    intro i hi j hj ht
    rcases Nat.lt_trichotomy i j with hij | rfl | hij
    · exact h1 i hi j hj hij ht
    · rw [Nat.xor_self, wBits_testBit, List.contains_iff_mem] at ht
      exact absurd rfl (hall 0 ht).1
    · rw [Nat.xor_comm] at ht
      rw [Nat.and_comm]
      exact h1 j hj i hi hij ht
  have hany : ∀ i < 891, ∃ j < 891, atLeast 16 (M.getD i 0 &&& M.getD j 0) = true ∧
      W.getD j 0 ≠ W.getD i 0 := by
    intro i hi
    rcases (rowK_sound _ _ _ (hrow i hi)).2 with h | ⟨s, hs, ha, hne⟩
    · obtain ⟨s, hs, ha, hne⟩ := anyK_sound _ _ h
      exact ⟨s, by omega, ha, hne⟩
    · rw [getD_drop] at ha hne
      simp only [List.length_drop] at hs
      exact ⟨i + 1 + s, by omega, ha, hne⟩
  have hA : (List.range 891).all (fun j => wtIdx[wtArr[j]!]! == j) = true := by
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.mp hj
    rw [beq_iff_eq, hwt j hj', wtIdx_get (hall _ (hmem j hj')).2]
    refine lastIdx_last hj' (hwt j hj') fun j' h1 h2 he => ?_
    rw [hwt j' h2] at he
    exact absurd (hinj j' j h2 hj' he) (by omega)
  have hB : (List.range 891).all modelOK = true := by
    rw [List.all_eq_true]
    intro i hi
    exact (hpin' i (List.mem_range.mp hi)).2.2
  have hC : (List.range 891).all (fun i => wtArr[i]! != 0 &&
      (List.range 891).any (fun j => adjM i j && wtArr[j]! != wtArr[i]!) &&
      (List.range 891).all (fun j => adjM i j || !isWt (wtArr[i]! ^^^ wtArr[j]!))) = true := by
    rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hwt i hi', bne_iff_ne]
      exact (hall _ (hmem i hi')).1
    · rw [List.any_eq_true]
      obtain ⟨j, hj, ha, hne⟩ := hany i hi'
      refine ⟨j, List.mem_range.mpr hj, ?_⟩
      unfold adjM
      rw [hmk i hi', hmk j hj, hwt i hi', hwt j hj, ha, Bool.true_and, bne_iff_ne]
      exact hne
    · rw [List.all_eq_true]
      intro j hj
      have hj' := List.mem_range.mp hj
      cases hw : isWt (wtArr[i]! ^^^ wtArr[j]!) with
      | false => rw [Bool.not_false, Bool.or_true]
      | true =>
        have hv : wtArr[i]! ^^^ wtArr[j]! ∈ W := by
          unfold isWt at hw
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
          rw [← hw.2, hwt _ hw.1]
          exact hmem _ hw.1
        rw [hwt i hi', hwt j hj', ← List.contains_iff_mem, ← wBits_testBit] at hv
        unfold adjM
        rw [hmk i hi', hmk j hj', hpair i hi' j hj' hv, Bool.true_or]
  unfold chkW
  rw [hA, hB, hC]
  rfl

end CFSG.SmithE.K
