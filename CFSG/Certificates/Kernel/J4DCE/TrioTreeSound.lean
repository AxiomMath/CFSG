module

public import Certificates.Data.Kernel.J4DCE.TrioTree
public import Certificates.Data.CFSGNative.J4DCE.Trio
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.J4DCE

open CFSG.KC.M24G

theorem firstOK_spec {TP TG : IxTree Nat} :
    ∀ {AX AY : List Nat} {p : Nat}, firstOK TP TG AX AY p = true →
      AX.length = AY.length ∧ ∀ i < AX.length,
        (AX.getD i 0 = 0 ∨ getT TP (AX.getD i 0) < p + i ∨
          (getT TP (AX.getD i 0) = p + i ∧ getT TG (AX.getD i 0) = 0)) ∧
        (AY.getD i 0 = 0 ∨ getT TP (AY.getD i 0) ≤ p + i)
  | [], [], _, _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | [], _ :: _, _, h => by simp [firstOK] at h
  | _ :: _, [], _, h => by simp [firstOK] at h
  | a :: AX, b :: AY, p, h => by
    simp only [firstOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨ha, hb⟩, h⟩ := h
    obtain ⟨hl, hs⟩ := firstOK_spec h
    refine ⟨by simp [hl], fun i hi => ?_⟩
    cases i with
    | zero =>
      simp only [List.getD_cons_zero, Nat.add_zero]
      refine ⟨?_, hb⟩
      rcases ha with (ha | ha) | ⟨ha1, ha2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ⟨ha1, ha2⟩)
    | succ i =>
      simp only [List.length_cons] at hi
      simp only [List.getD_cons_succ]
      have e : p + (i + 1) = p + 1 + i := by omega
      rw [e]
      exact hs i (by omega)

private abbrev tS : Type := Array Nat × Array Nat × Array Bool

@[expose] def treeStep (gi p : Nat) : Nat :=
  CFSG.J4DCE.Native.act
    (if gi == 0 then CFSG.YGroups.DCE.bofArr 24 CFSG.J4DCE.Native.xTab
      else CFSG.YGroups.DCE.bofArr 24 CFSG.J4DCE.Native.yTab) p

private abbrev tInner (n : Nat) (f : Nat → Nat → Nat) (p gi : Nat) (st : tS) : Id (ForInStep tS) :=
  if (decide (f gi p < n) && !st.2.2[f gi p]!) = true then
    pure (.yield (st.1.set! (f gi p) p, st.2.1.set! (f gi p) gi, st.2.2.set! (f gi p) true))
  else pure (.yield (st.1, st.2.1, st.2.2))

private abbrev tOuter (n : Nat) (f : Nat → Nat → Nat) (p : Nat) (st : tS) : Id (ForInStep tS) := do
  let r ← forIn (List.range' 0 2) (st.1, st.2.1, st.2.2) (tInner n f p)
  pure (.yield (r.1, r.2.1, r.2.2))

private abbrev tInit (n : Nat) : tS :=
  (Array.replicate n 0, Array.replicate n 0, (Array.replicate n false).set! 0 true)

private theorem bfsTree_loop :
    CFSG.J4DCE.Native.bfsTree () =
      (let s := Id.run (forIn (List.range' 0 (CFSG.J4DCE.Native.nTrios ()))
          (tInit (CFSG.J4DCE.Native.nTrios ())) (tOuter (CFSG.J4DCE.Native.nTrios ()) treeStep))
       (s.1, s.2.1)) := by
  unfold CFSG.J4DCE.Native.bfsTree
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  generalize CFSG.J4DCE.Native.nTrios () = N
  rfl

section Inv

variable {n : Nat} {f : Nat → Nat → Nat} {P G : Nat → Nat}

private def tInv (n : Nat) (P G : Nat → Nat) (k : Nat) (st : tS) : Prop :=
  st.1.size = n ∧ st.2.1.size = n ∧ st.2.2.size = n ∧ ∀ q < n,
    st.2.2[q]! = decide (q = 0 ∨ 2 * P q + G q < k) ∧
      st.1[q]! = (if 2 * P q + G q < k then P q else 0) ∧
      st.2.1[q]! = (if 2 * P q + G q < k then G q else 0)

private structure tHyp (n : Nat) (f : Nat → Nat → Nat) (P G : Nat → Nat) : Prop where
  lt : ∀ p < n, ∀ gi < 2, f gi p < n
  first : ∀ p < n, ∀ gi < 2, f gi p = 0 ∨ 2 * P (f gi p) + G (f gi p) ≤ 2 * p + gi
  tree : ∀ q, 0 < q → q < n → G q < 2 ∧ P q < q ∧ f (G q) (P q) = q
  p0 : P 0 = 0
  g0 : G 0 = 0

private theorem tInv_stable (hH : tHyp n f P G) {p gi q : Nat} (hp : p < n) (hgi : gi < 2)
    (hq : q < n) (hne : q ≠ f gi p) :
    decide (q = 0 ∨ 2 * P q + G q < 2 * p + gi + 1) = decide (q = 0 ∨ 2 * P q + G q < 2 * p + gi) ∧
      (if 2 * P q + G q < 2 * p + gi + 1 then P q else 0) =
        (if 2 * P q + G q < 2 * p + gi then P q else 0) ∧
      (if 2 * P q + G q < 2 * p + gi + 1 then G q else 0) =
        (if 2 * P q + G q < 2 * p + gi then G q else 0) := by
  by_cases h0 : q = 0
  · subst h0
    simp [hH.p0, hH.g0]
  · have hk : 2 * P q + G q ≠ 2 * p + gi := by
      intro e
      obtain ⟨hg, -, hf⟩ := hH.tree q (Nat.pos_of_ne_zero h0) hq
      have h1 : P q = p := by omega
      have h2 : G q = gi := by omega
      rw [h1, h2] at hf
      exact hne hf.symm
    have hiff : 2 * P q + G q < 2 * p + gi + 1 ↔ 2 * P q + G q < 2 * p + gi := by omega
    simp [hiff]

private theorem getElem!_set!_eq {α : Type} [Inhabited α] (a : Array α) {i j : Nat} (v : α)
    (hi : i < a.size) : (a.set! i v)[j]! = if i = j then v else a[j]! := by
  split
  · rename_i h
    subst h
    exact Array.getElem!_set!_self a i v hi
  · rename_i h
    exact Array.getElem!_set!_ne a i j v h

private theorem tInner_step (hH : tHyp n f P G) {p gi : Nat} (hp : p < n) (hgi : gi < 2)
    {st : tS} (hI : tInv n P G (2 * p + gi) st) :
    ∃ st', tInner n f p gi st = pure (.yield st') ∧ tInv n P G (2 * p + gi + 1) st' := by
  obtain ⟨h1, h2, h3, hv⟩ := hI
  have hq : f gi p < n := hH.lt p hp gi hgi
  by_cases hd : st.2.2[f gi p]! = true
  · refine ⟨st, ?_, h1, h2, h3, fun q hqn => ?_⟩
    · unfold tInner
      rw [if_neg (by simp [hd])]
    · by_cases hqe : q = f gi p
      · subst hqe
        have hd' := (hv (f gi p) hq).1
        rw [hd] at hd'
        have hc : f gi p = 0 ∨ 2 * P (f gi p) + G (f gi p) < 2 * p + gi := of_decide_eq_true hd'.symm
        rcases hc with hc | hc
        · obtain ⟨e1, e2, e3⟩ := hv 0 (by omega)
          rw [hc]
          refine ⟨?_, ?_, ?_⟩
          · rw [e1]
            simp
          · rw [e2]
            simp [hH.p0]
          · rw [e3]
            simp [hH.g0]
        · have hlt : 2 * P (f gi p) + G (f gi p) < 2 * p + gi + 1 := by omega
          obtain ⟨e1, e2, e3⟩ := hv (f gi p) hq
          rw [e1, e2, e3, if_pos hc, if_pos hc, if_pos hlt, if_pos hlt]
          simp [hc, hlt]
      · obtain ⟨s1, s2, s3⟩ := tInv_stable hH hp hgi hqn hqe
        obtain ⟨e1, e2, e3⟩ := hv q hqn
        exact ⟨e1.trans s1.symm, e2.trans s2.symm, e3.trans s3.symm⟩
  · have hd0 : st.2.2[f gi p]! = false := by simpa using hd
    have hc := (hv (f gi p) hq).1
    rw [hd0] at hc
    have hnc : ¬ (f gi p = 0 ∨ 2 * P (f gi p) + G (f gi p) < 2 * p + gi) :=
      of_decide_eq_false hc.symm
    have hz : f gi p ≠ 0 := fun e => hnc (Or.inl e)
    have hge : ¬ 2 * P (f gi p) + G (f gi p) < 2 * p + gi := fun e => hnc (Or.inr e)
    have hle := (hH.first p hp gi hgi).resolve_left hz
    obtain ⟨hg, -, -⟩ := hH.tree (f gi p) (Nat.pos_of_ne_zero hz) hq
    have hP : P (f gi p) = p := by omega
    have hG : G (f gi p) = gi := by omega
    refine ⟨(st.1.set! (f gi p) p, st.2.1.set! (f gi p) gi, st.2.2.set! (f gi p) true), ?_,
      by simp [Array.size_set!, h1], by simp [Array.size_set!, h2],
      by simp [Array.size_set!, h3], fun q hqn => ?_⟩
    · unfold tInner
      rw [if_pos (by simp [hq, hd0])]
    · simp only
      rw [getElem!_set!_eq _ _ (by omega), getElem!_set!_eq _ _ (by omega),
        getElem!_set!_eq _ _ (by omega)]
      by_cases hqe : f gi p = q
      · subst hqe
        have hlt : 2 * P (f gi p) + G (f gi p) < 2 * p + gi + 1 := by omega
        simp only [if_true, if_pos hlt, hP, hG]
        simp
      · rw [if_neg hqe, if_neg hqe, if_neg hqe]
        obtain ⟨s1, s2, s3⟩ := tInv_stable hH hp hgi hqn (Ne.symm hqe)
        obtain ⟨e1, e2, e3⟩ := hv q hqn
        exact ⟨e1.trans s1.symm, e2.trans s2.symm, e3.trans s3.symm⟩

private theorem tOuter_step (hH : tHyp n f P G) {p : Nat} (hp : p < n) {st : tS}
    (hI : tInv n P G (2 * p) st) :
    ∃ st', tOuter n f p st = pure (.yield st') ∧ tInv n P G (2 * (p + 1)) st' := by
  obtain ⟨s1, e1, hI1⟩ := tInner_step (gi := 0) hH hp (by decide) hI
  obtain ⟨s2, e2, hI2⟩ := tInner_step (gi := 1) hH hp (by decide) hI1
  refine ⟨s2, ?_, ?_⟩
  · unfold tOuter
    have hr : List.range' 0 2 = [0, 1] := rfl
    simp only [Prod.mk.eta]
    rw [hr, List.forIn_cons, e1]
    simp only [pure_bind]
    rw [List.forIn_cons, e2]
    simp
  · have e : 2 * (p + 1) = 2 * p + 1 + 1 := by omega
    rw [e]
    exact hI2

private theorem tOuter_loop (hH : tHyp n f P G) :
    ∀ (m s : Nat) (st : tS), s + m ≤ n → tInv n P G (2 * s) st →
      tInv n P G (2 * (s + m)) (Id.run (forIn (List.range' s m) st (tOuter n f)))
  | 0, s, st, _, hI => by simpa using hI
  | m + 1, s, st, hm, hI => by
    obtain ⟨st', e, hI'⟩ := tOuter_step hH (p := s) (by omega) hI
    rw [List.range'_succ, List.forIn_cons, e]
    simp only [pure_bind]
    have h := tOuter_loop hH m (s + 1) st' (by omega) hI'
    have e2 : s + 1 + m = s + (m + 1) := by omega
    rw [e2] at h
    exact h

private theorem tree_loop (hH : tHyp n f P G) (hn : 0 < n) :
    let s := Id.run (forIn (List.range' 0 n) (tInit n) (tOuter n f))
    s.1.size = n ∧ s.2.1.size = n ∧ ∀ q < n, s.1[q]! = P q ∧ s.2.1[q]! = G q := by
  have hI0 : tInv n P G (2 * 0) (tInit n) := by
    refine ⟨by simp [tInit], by simp [tInit], by simp [tInit, Array.size_set!], fun q hq => ?_⟩
    simp only [tInit, Nat.mul_zero, Nat.not_lt_zero, or_false, if_false]
    rw [getElem!_set!_eq _ _ (by simp; omega)]
    have hr : ∀ {α : Type} [Inhabited α] (v : α), (Array.replicate n v)[q]! = v := fun v => by
      rw [getElem!_pos (Array.replicate n v) q (by simp; omega)]
      simp
    rw [hr, hr]
    refine ⟨?_, rfl, rfl⟩
    by_cases h0 : q = 0
    · subst h0
      simp
    · rw [if_neg (Ne.symm h0)]
      simp [h0]
  have h := tOuter_loop hH n 0 (tInit n) (by omega) hI0
  intro s
  obtain ⟨h1, h2, -, hv⟩ := h
  refine ⟨h1, h2, fun q hq => ?_⟩
  obtain ⟨-, e2, e3⟩ := hv q hq
  have hlt : 2 * P q + G q < 2 * (0 + n) := by
    by_cases h0 : q = 0
    · subst h0
      rw [hH.p0, hH.g0]
      omega
    · obtain ⟨hg, hpq, -⟩ := hH.tree q (Nat.pos_of_ne_zero h0) hq
      omega
  rw [if_pos hlt] at e2 e3
  exact ⟨e2, e3⟩

end Inv

theorem bfsTree_eq {P G : Nat → Nat}
    (hlt : ∀ p < 3795, ∀ gi < 2, treeStep gi p < 3795)
    (hfirst : ∀ p < 3795, ∀ gi < 2,
      treeStep gi p = 0 ∨ 2 * P (treeStep gi p) + G (treeStep gi p) ≤ 2 * p + gi)
    (htree : ∀ q, 0 < q → q < 3795 → G q < 2 ∧ P q < q ∧ treeStep (G q) (P q) = q)
    (hp0 : P 0 = 0) (hg0 : G 0 = 0) :
    (CFSG.J4DCE.Native.bfsTree ()).1.size = 3795 ∧ (CFSG.J4DCE.Native.bfsTree ()).2.size = 3795 ∧
      ∀ q < 3795, (CFSG.J4DCE.Native.bfsTree ()).1[q]! = P q ∧
        (CFSG.J4DCE.Native.bfsTree ()).2[q]! = G q := by
  obtain ⟨h1, h2, h3⟩ := tree_loop (n := CFSG.J4DCE.Native.nTrios ()) (f := treeStep)
    ⟨hlt, hfirst, htree, hp0, hg0⟩ (by decide)
  rw [bfsTree_loop]
  dsimp only
  exact ⟨h1, h2, h3⟩

end CFSG.KC.J4DCE
