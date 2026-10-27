module

public import Certificates.Data.Kernel.OpsRenL
public import CFSG.Certificates.Kernel.OpsLayMcertSound

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native

@[expose] def RInv (c : Lay) (T : List (Option Nat)) (Rl Ro : List Nat) : Prop :=
  ∀ s r, T.getD s none = some r → getR c Rl s = getR c Ro r

theorem isReg_iff {x : Option Nat} {r : Nat} : isReg x r = true ↔ x = some r := by
  cases x with
  | none => simp [isReg]
  | some x =>
    constructor
    · intro h
      rw [Nat.eq_of_beq_eq_true h]
    · intro h
      cases h
      simp [isReg]

theorem getR_set_self (c : Lay) {R : List Nat} {t : Nat} (v : Nat) (ht : t < R.length) :
    getR c (R.set t v) t = v := by
  simp [getR, List.getD_eq_getElem?_getD, ht]

theorem getR_set_ne (c : Lay) {R : List Nat} {t s : Nat} (v : Nat) (h : t ≠ s) :
    getR c (R.set t v) s = getR c R s := by
  simp [getR, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem lt_of_getD_some {T : List (Option Nat)} {s r : Nat} (h : T.getD s none = some r) :
    s < T.length := by
  rw [List.getD_eq_getElem?_getD] at h
  by_contra hs
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

theorem renSet_getD {T : List (Option Nat)} {k t s r : Nat} (ht : t < T.length)
    (h : (renSet T k t).getD s none = some r) :
    (s = t ∧ r = k) ∨ (s ≠ t ∧ r ≠ k ∧ T.getD s none = some r) := by
  unfold renSet at h
  rw [List.getD_eq_getElem?_getD] at h
  by_cases hs : t = s
  · subst hs
    rw [List.getElem?_set_self (by simpa using ht)] at h
    simp only [Option.getD_some, Option.some.injEq] at h
    exact Or.inl ⟨rfl, h.symm⟩
  · rw [List.getElem?_set_ne hs, List.getElem?_map] at h
    right
    refine ⟨Ne.symm hs, ?_⟩
    rw [List.getD_eq_getElem?_getD]
    cases hx : T[s]? with
    | none => simp [hx] at h
    | some x =>
      rw [hx] at h
      simp only [Option.map_some, Option.getD_some] at h
      cases hb : isReg x k
      · rw [hb, cond_false] at h
        subst h
        refine ⟨fun hrk => ?_, rfl⟩
        subst hrk
        simp [isReg] at hb
      · rw [hb, cond_true] at h
        exact absurd h (by simp)

theorem renSet_sound {c : Lay} {T : List (Option Nat)} {Rl Ro : List Nat} {k t : Nat} (v : Nat)
    (hI : RInv c T Rl Ro) (hlen : T.length ≤ Rl.length) (ht : t < T.length)
    (hk : k < Ro.length) :
    RInv c (renSet T k t) (Rl.set t v) (Ro.set k v) ∧ (renSet T k t).length = T.length := by
  refine ⟨fun s r hs => ?_, by simp [renSet]⟩
  rcases renSet_getD ht hs with ⟨rfl, rfl⟩ | ⟨hst, hrk, hT⟩
  · rw [getR_set_self c v (by omega), getR_set_self c v hk]
  · rw [getR_set_ne c v (Ne.symm hst), getR_set_ne c v (Ne.symm hrk)]
    exact hI s r hT

theorem renStep_sound {c : Lay} {T T' : List (Option Nat)} {o l : Op} {Rl Ro : List Nat}
    (h : renStep T o l = some T') (hI : RInv c T Rl Ro) (hlen : T.length ≤ Rl.length)
    (hlt : Op.lt Ro.length o = true) :
    RInv c T' (Rl.set (Op.tgt l) (stepV c Rl l)) (Ro.set (Op.tgt o) (stepV c Ro o)) ∧
      T'.length = T.length := by
  cases o with
  | mul i j k =>
    cases l with
    | pow e a t => simp [renStep] at h
    | mul a b t =>
      simp only [renStep] at h
      cases hb : (isReg (T.getD a none) i && isReg (T.getD b none) j && decide (t < T.length))
      · rw [hb, cond_false] at h
        exact absurd h (by simp)
      · rw [hb, cond_true, Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        obtain ⟨⟨ha, hb'⟩, ht⟩ := hb
        simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
        have e : stepV c Rl (.mul a b t) = stepV c Ro (.mul i j k) := by
          simp only [stepV]
          rw [hI a i (isReg_iff.1 ha), hI b j (isReg_iff.1 hb')]
        rw [e]
        exact renSet_sound _ hI hlen ht hlt.2
  | pow e i k =>
    cases l with
    | mul a b t => simp [renStep] at h
    | pow e' a t =>
      simp only [renStep] at h
      cases hb : (Nat.beq e e' && isReg (T.getD a none) i && decide (t < T.length))
      · rw [hb, cond_false] at h
        exact absurd h (by simp)
      · rw [hb, cond_true, Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        obtain ⟨⟨he, ha⟩, ht⟩ := hb
        cases Nat.eq_of_beq_eq_true he
        simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
        have e : stepV c Rl (.pow e a t) = stepV c Ro (.pow e i k) := by
          simp only [stepV]
          rw [hI a i (isReg_iff.1 ha)]
        rw [e]
        exact renSet_sound _ hI hlen ht hlt.2

theorem renChunk_sound {c : Lay} :
    ∀ (ls : List (List Nat)) (T : List (Option Nat)) (P : List Op) (Rl Ro : List Nat)
      (T' : List (Option Nat)) (P' : List Op),
      renChunk T P ls = some (T', P') → RInv c T Rl Ro → T.length ≤ Rl.length →
      P.all (Op.lt Ro.length) = true →
      ∃ Q, P = Q ++ P' ∧ RInv c T' (Snd.runL c (ls.map opOf) Rl) (Snd.runL c Q Ro) ∧
        T'.length = T.length
  | [], T, P, Rl, Ro, T', P', h, hI, _, _ => by
    simp only [renChunk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, hI, rfl⟩
  | _ :: _, _, [], _, _, _, _, h, _, _, _ => by simp [renChunk] at h
  | l :: ls, T, o :: P, Rl, Ro, T', P', h, hI, hlen, hP => by
    cases hs : renStep T o (opOf l) with
    | none => simp [renChunk, hs] at h
    | some T1 =>
      simp only [renChunk, hs] at h
      rw [List.all_cons, Bool.and_eq_true] at hP
      obtain ⟨hI1, hl1⟩ := renStep_sound hs hI hlen hP.1
      have hlen1 : T1.length ≤ (Rl.set (Op.tgt (opOf l)) (stepV c Rl (opOf l))).length := by
        rw [List.length_set, hl1]
        exact hlen
      have hP1 : P.all (Op.lt (Ro.set (Op.tgt o) (stepV c Ro o)).length) = true := by
        rw [List.length_set]
        exact hP.2
      obtain ⟨Q, hQ, hI2, hl2⟩ := renChunk_sound ls T1 P _ _ T' P' h hI1 hlen1 hP1
      exact ⟨o :: Q, by rw [hQ, List.cons_append], hI2, by rw [hl2, hl1]⟩

theorem tabEq_eq : ∀ {T : List (Option Nat)} {outs : List Nat}, tabEq T outs = true →
    T = outs.map some
  | [], [], _ => rfl
  | x :: T, r :: rs, h => by
    simp only [tabEq, Bool.and_eq_true] at h
    rw [isReg_iff.1 h.1, tabEq_eq h.2]
    rfl
  | [], _ :: _, h => by simp [tabEq] at h
  | _ :: _, [], h => by simp [tabEq] at h

theorem getD_append_none (T : List (Option Nat)) (m s : Nat) :
    (T ++ List.replicate m none).getD s none = T.getD s none := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hs : s < T.length
  · rw [List.getElem?_append_left hs]
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate,
      List.getElem?_eq_none (by omega)]
    split <;> rfl

theorem getR_padR (c : Lay) {S : List Nat} {s : Nat} (n : Nat) (hs : s < S.length) :
    getR c (padR c S n) s = getR c S s := by
  unfold getR padR
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hs]

theorem renRun_sound {c : Lay} {outs : List Nat} {S : Nat → List Nat} :
    ∀ (cs : List RChunk) (j : Nat) (T : List (Option Nat)) (P : List Op) (Ro : List Nat),
      renRun outs T P cs = true → RInv c T (S j) Ro → T.length = (S j).length →
      P.all (Op.lt Ro.length) = true →
      (∀ i < cs.length, chunkV c (cs.getD i (0, [], [])) (S (j + i)) (S (j + i + 1)) = true) →
      outs.map (getR c (Snd.runL c P Ro)) = S (j + cs.length)
  | [], j, T, P, Ro, h, hI, hl, _, _ => by
    simp only [renRun, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨rfl, ht⟩ := h
    have hT := tabEq_eq ht
    subst hT
    simp only [List.length_nil, Nat.add_zero]
    apply List.ext_getElem
    · rw [List.length_map]
      simpa using hl
    · intro idx h1 h2
      rw [List.getElem_map]
      have h1' : idx < outs.length := by simpa using h1
      have hx : (outs.map some).getD idx none = some outs[idx] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h1']
        rfl
      change getR c Ro outs[idx] = _
      rw [← hI idx _ hx]
      unfold getR
      rw [Snd.getD_eq_of_lt _ h2]
  | (n, ls, out) :: cs, j, T, P, Ro, h, hI, hl, hP, hch => by
    simp only [renRun, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hn, h⟩ := h
    cases hr : renChunk (T ++ List.replicate (n - T.length) none) P ls with
    | none => simp [hr] at h
    | some q =>
      obtain ⟨T', P'⟩ := q
      simp only [hr] at h
      have hch0 := hch 0 (by simp)
      simp only [List.getD_cons_zero, Nat.add_zero] at hch0
      unfold chunkV at hch0
      rw [Snd.runC_eq] at hch0
      have hS1 := eq_of_eqL hch0
      have hIp : RInv c (T ++ List.replicate (n - T.length) none) (padR c (S j) n) Ro := by
        intro s r hs
        rw [getD_append_none] at hs
        have hsl := lt_of_getD_some hs
        rw [getR_padR c n (by omega)]
        exact hI s r hs
      have hlp : (T ++ List.replicate (n - T.length) none).length ≤ (padR c (S j) n).length := by
        simp only [padR, List.length_append, List.length_replicate]
        omega
      obtain ⟨Q, hQ, hI', _⟩ := renChunk_sound ls _ P _ Ro T' P' hr hIp hlp hP
      subst hQ
      have hIn : RInv c (out.map fun s => T'.getD s none) (S (j + 1)) (Snd.runL c Q Ro) := by
        intro s r hs
        rw [List.getD_eq_getElem?_getD, List.getElem?_map] at hs
        cases hx : out[s]? with
        | none => simp [hx] at hs
        | some x =>
          rw [hx] at hs
          simp only [Option.map_some, Option.getD_some] at hs
          rw [← hS1]
          have e : getR c (out.map (getR c (Snd.runL c (ls.map opOf) (padR c (S j) n)))) s =
              getR c (Snd.runL c (ls.map opOf) (padR c (S j) n)) x := by
            simp [getR, List.getD_eq_getElem?_getD, List.getElem?_map, hx]
          rw [e]
          exact hI' x r hs
      have hln : (out.map fun s => T'.getD s none).length = (S (j + 1)).length := by
        rw [← hS1, List.length_map, List.length_map]
      have hPn : P'.all (Op.lt (Snd.runL c Q Ro).length) = true := by
        rw [Snd.runL_length]
        rw [List.all_append, Bool.and_eq_true] at hP
        exact hP.2
      have ih := renRun_sound cs (j + 1) _ P' (Snd.runL c Q Ro) h hIn hln hPn (fun i hi => by
        have := hch (i + 1) (by simp only [List.length_cons]; omega)
        simp only [List.getD_cons_succ] at this
        rw [show j + 1 + i = j + (i + 1) by omega]
        exact this)
      rw [runL_append, ih, List.length_cons, show j + 1 + cs.length = j + (cs.length + 1) by omega]

theorem renOK_sound {c : Lay} {n A B : Nat} {P : List Op} {outs : List Nat} {cs : List RChunk}
    {S : Nat → List Nat} (hn : 2 ≤ n) (hP : P.all (Op.lt n) = true)
    (h : renOK outs P cs = true) (h0 : S 0 = [A, B])
    (hch : ∀ i < cs.length, chunkV c (cs.getD i (0, [], [])) (S i) (S (i + 1)) = true) :
    outs.map (getR c (Snd.runL c P (initR c A B n))) = S cs.length := by
  have hlen : (initR c A B n).length = n := by simp [initR]
  have key := renRun_sound (c := c) (S := S) cs 0 [some 0, some 1] P (initR c A B n) h ?_ ?_ ?_ ?_
  · simpa using key
  · intro s r hs
    rw [h0]
    rcases s with _ | _ | s
    · simp only [List.getD_cons_zero, Option.some.injEq] at hs
      subst hs
      simp [getR, initR, List.getD_eq_getElem?_getD, show 0 < n by omega]
    · simp only [List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq] at hs
      subst hs
      simp [getR, initR, List.getD_eq_getElem?_getD, show 1 < n by omega]
    · simp [List.getD_eq_getElem?_getD] at hs
  · rw [h0]
    rfl
  · rw [hlen]
    exact hP
  · intro i hi
    simpa using hch i hi

end CFSG.KC.OpsLayK

end
