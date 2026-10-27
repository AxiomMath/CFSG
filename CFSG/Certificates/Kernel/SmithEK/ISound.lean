module

public import Certificates.Data.Kernel.SmithEKI
public import CFSG.Certificates.Kernel.SmithEK.SpanSound

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE
open CFSG.SmithL6.K (maskOf maskOf_testBit lastIdx)

theorem reduceBy_cons (be : Nat × Nat) (E : List (Nat × Nat)) (v : Nat) :
    reduceBy (be :: E) v = reduceBy E (if v.testBit be.1 then v ^^^ be.2 else v) := rfl

theorem reduceBy_xor : ∀ (E : List (Nat × Nat)) (a b : Nat),
    reduceBy E (a ^^^ b) = reduceBy E a ^^^ reduceBy E b
  | [], a, b => rfl
  | be :: E, a, b => by
    rw [reduceBy_cons, reduceBy_cons, reduceBy_cons, ← reduceBy_xor E]
    congr 1
    rw [Nat.testBit_xor]
    cases ha : a.testBit be.1 <;> cases hb : b.testBit be.1 <;> simp <;> ac_nf <;>
      (try simp only [Nat.xor_self, Nat.xor_zero])

theorem eq_of_xor_eq_zero {v y : Nat} (h : v ^^^ y = 0) : v = y := by
  have := congrArg (· ^^^ y) h
  simpa [Nat.xor_assoc, Nat.xor_self] using this

theorem reduceBy_zero : ∀ (E : List (Nat × Nat)), reduceBy E 0 = 0
  | [] => rfl
  | be :: E => by rw [reduceBy_cons, Nat.zero_testBit]; exact reduceBy_zero E

theorem reduceBy_span : ∀ (E : List (Nat × Nat)) (v : Nat),
    ∃ c < 2 ^ E.length, reduceBy E v = v ^^^ applyL (E.map (·.2)) c
  | [], v => ⟨0, by simp, by simp [reduceBy, applyL]⟩
  | be :: E, v => by
    obtain ⟨c, hc, h⟩ := reduceBy_span E (if v.testBit be.1 then v ^^^ be.2 else v)
    refine ⟨(if v.testBit be.1 then 1 else 0) + 2 * c, ?_, ?_⟩
    · rw [List.length_cons, pow_succ]
      split_ifs <;> omega
    · rw [reduceBy_cons, h, List.map_cons]
      have e : ∀ c', applyL (be.2 :: E.map (·.2)) c' =
          (if c'.testBit 0 then be.2 else 0) ^^^ applyL (E.map (·.2)) (c' / 2) := fun _ => rfl
      rw [e]
      have h0 : ((if v.testBit be.1 then 1 else 0) + 2 * c).testBit 0 = v.testBit be.1 := by
        rw [Nat.testBit_zero]
        split_ifs with hv <;> simp [hv] <;> omega
      have h1 : ((if v.testBit be.1 then 1 else 0) + 2 * c) / 2 = c := by split_ifs <;> omega
      rw [h0, h1]
      split_ifs <;> simp [Nat.xor_assoc]

theorem applyL_map_lin {f : Nat → Nat} (h0 : f 0 = 0) (hx : ∀ a b, f (a ^^^ b) = f a ^^^ f b) :
    ∀ (L : List Nat) (c : Nat), applyL (L.map f) c = f (applyL L c)
  | [], _ => h0.symm
  | x :: L, c => by
    have e : ∀ (l : List Nat) (y c : Nat),
        applyL (y :: l) c = (if c.testBit 0 then y else 0) ^^^ applyL l (c / 2) := fun _ _ _ => rfl
    rw [List.map_cons, e, e, hx, applyL_map_lin h0 hx L]
    split_ifs <;> simp [h0]

theorem xor_bit_double (b x : Nat) (hb : b < 2) : b ^^^ 2 * x = b + 2 * x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp <;> omega
  · rw [← Nat.testBit_div_two, ← Nat.testBit_div_two (b + 2 * x), ← Nat.testBit_div_two (2 * x)]
    rw [show b / 2 = 0 by omega, show (b + 2 * x) / 2 = x by omega,
      show 2 * x / 2 = x by omega, Nat.zero_testBit, Bool.false_xor]

theorem two_mul_xor (a b : Nat) : 2 * (a ^^^ b) = 2 * a ^^^ 2 * b := by
  have h := Nat.shiftLeft_xor_distrib (a := a) (b := b) (i := 1)
  simp only [Nat.shiftLeft_eq, pow_one] at h
  rw [Nat.mul_comm 2, Nat.mul_comm 2 a, Nat.mul_comm 2 b]
  exact h

theorem applyL_pow : ∀ (n v : Nat), v < 2 ^ n → applyL ((List.range n).map (2 ^ ·)) v = v
  | 0, v, hv => by simp at hv; subst hv; rfl
  | n + 1, v, hv => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have e : (fun m => 2 ^ m) ∘ Nat.succ = (fun x => 2 * x) ∘ (fun m => 2 ^ m) := by
      funext m
      simp [pow_succ, Nat.mul_comm]
    have e2 : ∀ (l : List Nat) (y c : Nat),
        applyL (y :: l) c = (if c.testBit 0 then y else 0) ^^^ applyL l (c / 2) := fun _ _ _ => rfl
    rw [e, ← List.map_map, e2, applyL_map_lin (f := fun x => 2 * x) rfl two_mul_xor,
      applyL_pow n (v / 2) (by rw [pow_succ] at hv; omega)]
    rw [pow_zero, Nat.testBit_zero]
    have hb : (if decide (v % 2 = 1) = true then 1 else 0) = v % 2 := by
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    rw [hb, xor_bit_double _ _ (Nat.mod_lt _ (by omega))]
    omega

theorem applyL_lt {B : List Nat} {n : Nat} (hB : ∀ b ∈ B, b < 2 ^ n) :
    ∀ c, applyL B c < 2 ^ n := by
  induction B with
  | nil => intro c; exact Nat.two_pow_pos n
  | cons x B ih =>
    intro c
    have e : applyL (x :: B) c = (if c.testBit 0 then x else 0) ^^^ applyL B (c / 2) := rfl
    rw [e]
    apply Nat.xor_lt_two_pow
    · split_ifs
      · exact hB x (by simp)
      · exact Nat.two_pow_pos n
    · exact ih (fun b hb => hB b (by simp [hb])) _

theorem spanL_cons (b : Nat) (B : List Nat) :
    spanL (b :: B) = spanL B ++ (spanL B).map (b ^^^ ·) := rfl

theorem applyL_mem_spanL : ∀ (B : List Nat) (c : Nat), c < 2 ^ B.length → applyL B c ∈ spanL B
  | [], c, hc => by simp at hc; subst hc; simp [spanL, applyL]
  | b :: B, c, hc => by
    have e : applyL (b :: B) c = (if c.testBit 0 then b else 0) ^^^ applyL B (c / 2) := rfl
    have ih := applyL_mem_spanL B (c / 2) (by rw [List.length_cons, pow_succ] at hc; omega)
    rw [e, spanL_cons, List.mem_append]
    split_ifs
    · exact Or.inr (List.mem_map.2 ⟨_, ih, rfl⟩)
    · rw [Nat.zero_xor]
      exact Or.inl ih

theorem spanM_testBit (B : List Nat) (v : Nat) : (spanM B).testBit v = (spanL B).contains v := by
  unfold spanM maskOf
  rw [maskOf_testBit, Nat.zero_testBit, Bool.false_or]

theorem rowI_sound (W1 p m : Nat) : ∀ (P Ms : List Nat), rowI W1 p m P Ms = true →
    ∀ j < P.length, pairI W1 p m (P.getD j 0) (Ms.getD j 0) = true
  | [], _, _, j, hj => by simp at hj
  | q :: P, Ms, h, j, hj => by
    have e : rowI W1 p m (q :: P) Ms = (pairI W1 p m q (Ms.headD 0) && rowI W1 p m P Ms.tail) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases j with _ | j
    · rw [getD_zero Ms]
      exact h.1
    · rw [getD_succ Ms]
      exact rowI_sound W1 p m P Ms.tail h.2 j (by simpa using hj)

theorem rowsI_sound (W1 : Nat) : ∀ (R S Pt Mt : List Nat), rowsI W1 R S Pt Mt = true →
    ∀ i < R.length, rowI W1 (R.getD i 0) (S.getD i 0) (Pt.drop i) (Mt.drop i) = true
  | [], _, _, _, _, i, hi => by simp at hi
  | p :: R, S, Pt, Mt, h, i, hi => by
    have e : rowsI W1 (p :: R) S Pt Mt =
        (rowI W1 p (S.headD 0) Pt Mt && rowsI W1 R S.tail Pt.tail Mt.tail) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases i with _ | i
    · rw [getD_zero S]
      exact h.1
    · rw [getD_succ S, ← List.drop_tail (l := Pt), ← List.drop_tail (l := Mt)]
      exact rowsI_sound W1 R S.tail Pt.tail Mt.tail h.2 i (by simpa using hi)

theorem chunkI_sound {W1 : Nat} {P Ms : List Nat} {a n : Nat} (h : chunkI W1 P Ms a n = true)
    {r : Nat} (hr : r < n) {j : Nat} (hj : a + r < j) (hjl : j < P.length) :
    pairI W1 (P.getD (a + r) 0) (Ms.getD (a + r) 0) (P.getD j 0) (Ms.getD j 0) = true := by
  have e := rowsI_sound W1 _ _ _ _ h r (by simp; omega)
  rw [getD_drop_take _ hr, getD_drop_take _ hr, List.drop_drop, List.drop_drop] at e
  have e' := rowI_sound W1 _ _ _ _ e (j - (a + 1 + r)) (by simp; omega)
  rw [getD_drop, getD_drop, show a + 1 + r + (j - (a + 1 + r)) = j by omega] at e'
  exact e'

theorem basOK_sound (T : List (List (List (List Nat)))) : ∀ (P : List Nat) (Bs : List (List Nat)),
    basOK T P Bs = true → Bs.length = P.length ∧
      ∀ k < P.length, basRow T (P.getD k 0) (Bs.getD k []) = true
  | [], Bs, h => by
    have e : basOK T [] Bs = Bs.isEmpty := rfl
    rw [e, List.isEmpty_iff] at h
    simp [h]
  | p :: P, [], h => by
    have e : basOK T (p :: P) [] = (basRow T p [] && basOK T P []) := rfl
    rw [e] at h
    simp [basRow] at h
  | p :: P, B :: Bs, h => by
    have e : basOK T (p :: P) (B :: Bs) = (basRow T p B && basOK T P Bs) := rfl
    rw [e, Bool.and_eq_true] at h
    obtain ⟨hl, hk⟩ := basOK_sound T P Bs h.2
    refine ⟨by simp [hl], fun k hk' => ?_⟩
    rcases k with _ | k
    · simpa using h.1
    · simpa using hk k (by simpa using hk')

theorem spanArr_get {k : Nat} (hk : k < 693) : spanArr[k]! = spanData (tvCols k) := by
  rw [getElem!_pos spanArr k (by simp [spanArr, tvArr, hk])]
  simp [spanArr, tvArr]

theorem spanData_of {L : List Nat} (hL : L.length = 20) :
    (spanData L.toArray).basis = (basL L).toArray ∧
    (spanData L.toArray).syn = ((List.range 20).map (2 ^ ·) |>.map
      (reduceBy ((gensL L).foldl insertVec []))).toArray := by
  have hE : echelon L.toArray = (gensL L).foldl insertVec [] := by
    unfold echelon
    rw [gensOf_toList hL]
  refine ⟨by simp [spanData, hE, basL], ?_⟩
  apply Array.ext
  · simp [spanData]
  · intro i h1 h2
    simp [spanData, hE]

theorem basL_length_echelon (L : List Nat) :
    (basL L).length = ((gensL L).foldl insertVec []).length := by
  simp [basL]

theorem chkI_of {T : List (List (List (List Nat)))} {P W : List Nat} {Bs : List (List Nat)}
    (hP : uPts () = P.toArray) (hPl : P.length = 693)
    (hT : ∀ k < 693, tvCols k = (tvW T (P.getD k 0)).toArray)
    (hTl : ∀ p, (tvW T p).length = 20)
    (hB : basOK T P Bs = true)
    (hpair : ∀ k < 693, ∀ l < 693, k < l → pairI (wBits W ||| 1) (P.getD k 0)
      (spanM (Bs.getD k [])) (P.getD l 0) (spanM (Bs.getD l [])) = true)
    (hW : ∀ v ∈ W, isWt v = true) : chkI = true := by
  obtain ⟨-, hrow⟩ := basOK_sound T P Bs hB
  unfold chkI
  rw [List.all_eq_true]
  intro k hk
  have hk' : k < 693 := List.mem_range.1 hk
  rw [List.all_eq_true]
  intro l hl
  have hl' : l < 693 := List.mem_range.1 hl
  rcases Nat.lt_or_ge k l with hkl | hkl
  swap
  · simp [hkl]
  rw [Bool.or_eq_true]
  right
  have hr := fun k (hk : k < 693) => hrow k (by omega)
  have bk := hr k hk'
  have bl := hr l hl'
  unfold basRow at bk bl
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at bk bl
  obtain ⟨⟨ek, lk⟩, ltk⟩ := bk
  obtain ⟨⟨el, -⟩, -⟩ := bl
  rw [spanArr_get hk', spanArr_get hl', hT k hk', hT l hl']
  obtain ⟨hbk, -⟩ := spanData_of (hTl (P.getD k 0))
  obtain ⟨-, hsl⟩ := spanData_of (hTl (P.getD l 0))
  rw [hbk, hsl, ek, hP, getElem!_toArray, getElem!_toArray]
  generalize hEl : (gensL (tvW T (P.getD l 0))).foldl insertVec [] = El at hsl el
  have hBl : Bs.getD l [] = El.map (·.2) := by rw [← el, basL, hEl]
  have hp := hpair k hk' l hl' hkl
  rw [List.all_eq_true]
  intro d hd
  have hd' : d < 2 ^ (Bs.getD k []).length := by rw [lk]; simpa using hd
  rw [Bool.or_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
  have hfun : applyCols ((List.range 20).map (2 ^ ·) |>.map (reduceBy El)).toArray =
      applyL ((List.range 20).map (2 ^ ·) |>.map (reduceBy El)) := funext (applyCols_toArray _)
  rw [hfun, List.map_toArray]
  simp only [applyCols_toArray]
  rw [← applyL_comp]
  generalize hv : applyL (Bs.getD k []) d = v
  have hv20 : v < 2 ^ 20 := hv ▸ applyL_lt ltk d
  rw [applyL_map_lin (reduceBy_zero El) (reduceBy_xor El), applyL_pow 20 v hv20]
  by_cases h0 : reduceBy El v = 0
  swap
  · exact Or.inl h0
  right
  obtain ⟨c, hc, hce⟩ := reduceBy_span El v
  rw [h0, eq_comm] at hce
  replace hce := eq_of_xor_eq_zero hce
  have mk : (spanM (Bs.getD k [])).testBit v = true := by
    rw [spanM_testBit, List.contains_iff_mem, ← hv]
    exact applyL_mem_spanL _ _ hd'
  have ml : (spanM (Bs.getD l [])).testBit v = true := by
    rw [spanM_testBit, List.contains_iff_mem, hce, hBl]
    exact applyL_mem_spanL _ _ (by simpa using hc)
  unfold pairI at hp
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hp
  rcases hp with h1 | ⟨hh, hI⟩
  · have := congrArg (Nat.testBit · v) h1
    simp only [Nat.testBit_and, mk, ml, Bool.and_self] at this
    left
    exact beq_iff_eq.2 (Nat.testBit_one_eq_true_iff_self_eq_zero.1 this.symm)
  · have hw : (wBits W ||| 1).testBit v = true := by
      have := congrArg (Nat.testBit · v) hI
      simp only [Nat.testBit_and, mk, ml, Bool.and_self, Bool.true_and] at this
      exact this
    rw [Nat.testBit_or, wBits_testBit, Bool.or_eq_true, List.contains_iff_mem] at hw
    rcases hw with hw | hw
    · by_cases hz : v = 0
      · left
        simpa using hz
      · right
        rw [Bool.and_eq_true, beq_iff_eq]
        exact ⟨hh, hW v hw⟩
    · left
      exact beq_iff_eq.2 (Nat.testBit_one_eq_true_iff_self_eq_zero.1 hw)

theorem lastIdx_spec {f : Nat → Nat} {x d : Nat} :
    ∀ N, (∃ j < N, f j = x) → lastIdx f x d N < N ∧ f (lastIdx f x d N) = x
  | 0, ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero j)
  | N + 1, ⟨j, hj, hf⟩ => by
    unfold lastIdx
    by_cases hN : f N = x
    · rw [if_pos hN]
      exact ⟨Nat.lt_succ_self N, hN⟩
    · rw [if_neg hN]
      have hj' : j < N := by
        rcases Nat.lt_or_ge j N with h | h
        · exact h
        · exact absurd (show j = N by omega ▸ hf) hN
      obtain ⟨a, b⟩ := lastIdx_spec N ⟨j, hj', hf⟩
      exact ⟨by omega, b⟩

theorem isWt_of {W M : List Nat} (hlen : W.length = 891) (hok : wListOK W = true)
    (hpin : ∀ i < 891, pinRow (decW (wData.toList.getD i 0)) (W.getD i 0) (M.getD i 0) = true) :
    ∀ v ∈ W, isWt v = true := by
  obtain ⟨hall, -⟩ := wListOK_sound hok
  have hwt : ∀ i < 891, wtArr[i]! = W.getD i 0 := by
    intro i hi
    have e := hpin i hi
    unfold pinRow at e
    simp only [Bool.and_eq_true, beq_iff_eq] at e
    have hw : wB i = decW (wData.toList.getD i 0) := by rw [wB_eq, CFSG.SmithL6.Kernel.get0]
    rw [wtArr_get hi]
    unfold wt
    rw [hw, e.1.1]
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hj' : j < 891 := by omega
  have hgj : W[j] = W.getD j 0 := by simp [List.getD_eq_getElem?_getD, hj]
  have hex : ∃ j' < 891, (fun j => wtArr[j]!) j' = W[j] := ⟨j, hj', by beta_reduce; rw [hwt j hj', hgj]⟩
  obtain ⟨h1, h2⟩ := lastIdx_spec (d := 891) 891 hex
  unfold isWt
  rw [wtIdx_get (hall _ hv).2]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨h1, h2⟩

end CFSG.SmithE.K
