module

public import CFSG.Certificates.Kernel.GilmanCensus.CandSound
public import CFSG.Certificates.Kernel.GilmanCensus.PlaneSound
public import CFSG.Certificates.Kernel.GilmanCensus.SimSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

theorem aLoop_eq (i : Nat) : ∀ (R : List (List Nat)) (s c : Nat),
    ((List.range' 0 R.length).foldl (fun p j => (p.1 + p.2 % 3 * (R.getD j []).getD i 0, p.2 / 3))
      (s, c)).1 = s + aEnt i R c
  | [], s, c => by simp [aEnt]
  | r :: R, s, c => by
    rw [List.length_cons, List.range'_succ, List.foldl_cons, foldl_range'_succ]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [aLoop_eq i R]
    simp only [aEnt]
    omega

theorem aVec_toList (d : Nat) (dual : Array (Array Nat)) (code : Nat) :
    (aVec d dual code).toList = (List.range d).map fun i => aEnt i (LL dual) code % 3 := by
  unfold aVec
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [Array.toList_ofFn, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, Id.run_pure, getEnt]
    have := aLoop_eq i (LL dual) 0 code
    rw [length_LL, Nat.zero_add] at this
    rw [← this]
    rfl

theorem orFold_const {α β : Type} (g : β → α → β) (p : α → Bool) : ∀ (l : List α) (s : β),
    orFold g (fun _ a => p a) l s = l.any p
  | [], _ => rfl
  | a :: l, s => by rw [orFold, orFold_const g p l, List.any_cons]

@[expose] def tstM (dt : Data) (a : Array Nat) (cands : Array C4) (j : Nat) : Bool :=
  (kerPure dt cands[j]!.2.1).size == 1 || (kerPure dt cands[j]!.2.1).any fun k => dot3 a k != 0

@[expose] def badM (dt : Data) (a : Array Nat) (cands : Array C4) (j : Nat) : Bool :=
  tstM dt a cands j && (kerPure dt cands[j]!.2.1).size != 1

theorem sim_avail (dt : Data) (a : Array Nat) (cands : Array C4) :
    Sim dt (forIn [:cands.size] (#[] : Array Nat) (availBody dt a cands))
      ((List.range' 0 cands.size).filter (tstM dt a cands)).toArray
      ((List.range' 0 cands.size).any (badM dt a cands)) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have h := sim_forIn dt (fun r j => if tstM dt a cands j = true then r.push j else r)
    (fun _ j => badM dt a cands j) (availBody dt a cands) (fun j s => by
      unfold availBody
      refine sim_congr (sim_bind (sim_kernelM dt _) ?_) rfl (Bool.false_or _)
      unfold badM tstM
      by_cases t : ((kerPure dt cands[j]!.2.1).size == 1 ||
          (kerPure dt cands[j]!.2.1).any fun k => dot3 a k != 0) = true
      · rw [if_pos t, if_pos t, t, Bool.true_and]
        by_cases u : ((kerPure dt cands[j]!.2.1).size != 1) = true
        · rw [if_pos u, u]
          exact sim_bind (sim_markBad dt) (sim_pure dt _)
        · rw [if_neg u]
          rw [Bool.not_eq_true] at u
          rw [u]
          exact sim_pure dt _
      · rw [if_neg t, if_neg t]
        rw [Bool.not_eq_true] at t
        rw [t, Bool.false_and]
        exact sim_pure dt _) (List.range' 0 cands.size) #[]
  rw [orFold_const, foldl_push_filter, Array.empty_append] at h
  exact h

@[expose] def availM (dt : Data) (a : Array Nat) (cands : Array C4) : Array Nat :=
  ((List.range' 0 cands.size).filter (tstM dt a cands)).toArray

@[expose] def patStepM (dt : Data) (cands : Array C4) (dual : Array (Array Nat))
    (patterns : Array (Array Nat)) (code : Nat) : Array (Array Nat) :=
  let a := aVec dt.d dual code
  let nz := a.any (· != 0)
  if dt.d - (if nz then 1 else 0) < 4 then patterns
  else if (nz && line3 a != a) = true then patterns
  else if (!patterns.contains (availM dt a cands)) = true then patterns.push (availM dt a cands)
  else patterns

@[expose] def patBadM (dt : Data) (cands : Array C4) (dual : Array (Array Nat)) (code : Nat) : Bool :=
  let a := aVec dt.d dual code
  let nz := a.any (· != 0)
  if dt.d - (if nz then 1 else 0) < 4 then false
  else if (nz && line3 a != a) = true then false
  else (List.range' 0 cands.size).any (badM dt a cands)

theorem sim_patBody (dt : Data) (cands : Array C4) (dual : Array (Array Nat)) (code : Nat)
    (patterns : Array (Array Nat)) :
    Sim dt (patBody dt cands dual code patterns)
      (ForInStep.yield (patStepM dt cands dual patterns code)) (patBadM dt cands dual code) := by
  unfold patBody patStepM patBadM
  dsimp only
  generalize aVec dt.d dual code = a
  generalize a.any (fun x => x != 0) = nz
  by_cases c1 : dt.d - (if nz = true then 1 else 0) < 4
  · rw [if_pos c1, if_pos c1, if_pos c1]
    exact sim_pure dt _
  rw [if_neg c1, if_neg c1, if_neg c1]
  by_cases c2 : (nz && line3 a != a) = true
  · rw [if_pos c2, if_pos c2, if_pos c2]
    exact sim_pure dt _
  rw [if_neg c2, if_neg c2, if_neg c2]
  rw [← Bool.or_false ((List.range' 0 cands.size).any _)]
  refine sim_bind (sim_avail dt _ cands) ?_
  unfold availM
  split <;> exact sim_pure dt _

theorem sim_patLoop (dt : Data) (cands : Array C4) (dual : Array (Array Nat)) :
    Sim dt (forIn [:3 ^ dual.size] (#[] : Array (Array Nat)) (patBody dt cands dual))
      ((List.range' 0 (3 ^ dual.size)).foldl (patStepM dt cands dual) #[])
      ((List.range' 0 (3 ^ dual.size)).any (patBadM dt cands dual)) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have h := sim_forIn dt (patStepM dt cands dual) (fun _ code => patBadM dt cands dual code)
    (patBody dt cands dual) (fun code s => sim_patBody dt cands dual code s)
    (List.range' 0 (3 ^ dual.size)) #[]
  rw [orFold_const] at h
  exact h

@[expose] def CandRel (dk : DK) (cands : Array C4) (cs : List Cand) : Prop :=
  cands = (cs.map cv).toArray ∧ ∀ c ∈ cs, c.2.2.2.2.2 = kernelK dk c.2.1 ∧ c.2.1 < 2 ^ dk.N

abbrev cand0 : Cand := ([], 0, false, false, false, [])

@[expose] def kjK (cs : List Cand) (j : Nat) : List (List Nat) := (cs.getD j cand0).2.2.2.2.2

@[expose] def tstK (cs : List Cand) (a : List Nat) (j : Nat) : Bool :=
  (kjK cs j).length == 1 || (kjK cs j).any fun k => dot3K a k != 0

theorem cand_ker {dt : Data} {dk : DK} (h : Rel dt dk) {cands : Array C4} {cs : List Cand}
    (hc : CandRel dk cands cs) (j : Nat) (hj : j < cs.length) :
    LL (kerPure dt cands[j]!.2.1) = kjK cs j := by
  obtain ⟨e, hm⟩ := hc
  have hmem : cs[j] ∈ cs := List.getElem_mem hj
  have hK : cands[j]!.2.1 = cs[j].2.1 := by
    subst e
    rw [getElem!_pos _ j (by simpa using hj)]
    simp [cv]
  unfold kjK
  rw [getD_lt cs cand0 hj, hK, (hm _ hmem).1, kerPure_eq h _ (hm _ hmem).2]

theorem arr_any_eq (a : Array (Array Nat)) (p : Array Nat → Bool) (q : List Nat → Bool)
    (hpq : ∀ v, p v = q v.toList) : a.any p = (LL a).any q := by
  rw [← Array.any_toList, LL, List.any_map]
  congr 1
  funext v
  exact hpq v

theorem tst_eq {dt : Data} {dk : DK} (h : Rel dt dk) {cands : Array C4} {cs : List Cand}
    (hc : CandRel dk cands cs) (a : Array Nat) (j : Nat) (hj : j < cs.length) :
    tstM dt a cands j = tstK cs a.toList j := by
  unfold tstM tstK
  rw [arr_any_eq _ _ (fun k => dot3K a.toList k != 0) (fun v => by rw [dot3_eq]), ← length_LL,
    cand_ker h hc j hj]

theorem bad_eq {dt : Data} {dk : DK} (h : Rel dt dk) {cands : Array C4} {cs : List Cand}
    (hc : CandRel dk cands cs) (a : Array Nat) (j : Nat) (hj : j < cs.length) :
    badM dt a cands j = (tstK cs a.toList j && (kjK cs j).length != 1) := by
  unfold badM
  rw [tst_eq h hc a j hj, ← length_LL, cand_ker h hc j hj]

theorem csize {dk : DK} {cands : Array C4} {cs : List Cand} (hc : CandRel dk cands cs) :
    cands.size = cs.length := by
  rw [hc.1]
  simp

theorem availM_eq {dt : Data} {dk : DK} (h : Rel dt dk) {cands : Array C4} {cs : List Cand}
    (hc : CandRel dk cands cs) (a : Array Nat) :
    (availM dt a cands).toList = (List.range cs.length).filter (tstK cs a.toList) := by
  unfold availM
  rw [List.toList_toArray, csize hc, List.range_eq_range']
  apply List.filter_congr
  intro j hj
  rw [List.mem_range'] at hj
  exact tst_eq h hc a j (by omega)

@[expose] def patStepK (dk : DK) (dual : List (List Nat)) (cands : List Cand)
    (st : List (List Nat) × Bool) (code : Nat) : List (List Nat) × Bool :=
  let a := (List.range dk.d).map fun i => aEnt i dual code % 3
  let nz := a.any (· != 0)
  if dk.d - (if nz then 1 else 0) < 4 then st
  else if nz && line3K a != a then st
  else
    let avail := (List.range cands.length).filter fun j =>
      let kj := ((cands.getD j ([], 0, false, false, false, [])).2.2.2.2.2)
      kj.length == 1 || kj.any fun k => dot3K a k != 0
    let bad := avail.any fun j => ((cands.getD j ([], 0, false, false, false, [])).2.2.2.2.2).length != 1
    (if st.1.contains avail then st.1 else st.1 ++ [avail], st.2 || bad)

theorem patternsK_eq (dk : DK) (dual : List (List Nat)) (cands : List Cand) :
    patternsK dk dual cands = (List.range (3 ^ dual.length)).foldl (patStepK dk dual cands) ([], false) :=
  rfl

theorem arr_bne (a b : Array Nat) : (a != b) = (a.toList != b.toList) := by
  rw [bne, bne, arr_beq_toList]

theorem pat_step {dt : Data} {dk : DK} (h : Rel dt dk) {cands : Array C4} {cs : List Cand}
    (hc : CandRel dk cands cs) (dual : Array (Array Nat)) (code : Nat)
    (pats : Array (Array Nat)) (st : List (List Nat) × Bool) (hp : pats.toList.map Array.toList = st.1) :
    (patStepM dt cands dual pats code).toList.map Array.toList = (patStepK dk (LL dual) cs st code).1 ∧
      (st.2 || patBadM dt cands dual code) = (patStepK dk (LL dual) cs st code).2 := by
  have ha := aVec_toList dt.d dual code
  rw [h.d] at ha
  unfold patStepM patBadM patStepK
  dsimp only
  rw [h.d, ← ha, ← Array.any_toList, arr_bne, line3_eq]
  generalize hnz : (aVec dk.d dual code).toList.any (fun x => x != 0) = nz
  by_cases c1 : dk.d - (if nz = true then 1 else 0) < 4
  · rw [if_pos c1, if_pos c1, if_pos c1]
    exact ⟨hp, Bool.or_false _⟩
  rw [if_neg c1, if_neg c1, if_neg c1]
  by_cases c2 : (nz && line3K (aVec dk.d dual code).toList != (aVec dk.d dual code).toList) = true
  · rw [if_pos c2, if_pos c2, if_pos c2]
    exact ⟨hp, Bool.or_false _⟩
  rw [if_neg c2, if_neg c2, if_neg c2]
  have hav := availM_eq h hc (aVec dk.d dual code)
  have hlen := csize hc
  refine ⟨?_, ?_⟩
  · rw [arr_contains, hp]
    have e : (List.range cs.length).filter (fun j =>
        let kj := (cs.getD j ([], 0, false, false, false, [])).2.2.2.2.2
        kj.length == 1 || kj.any fun k => dot3K (aVec dk.d dual code).toList k != 0) =
        (availM dt (aVec dk.d dual code) cands).toList := by rw [hav]; rfl
    rw [e]
    cases st.1.contains (availM dt (aVec dk.d dual code) cands).toList
    · simp [← hp]
    · simp [← hp]
  · have e2 : (List.range' 0 cands.size).any (badM dt (aVec dk.d dual code) cands) =
        ((List.range cs.length).filter (tstK cs (aVec dk.d dual code).toList)).any
          (fun j => (kjK cs j).length != 1) := by
      rw [List.any_filter, hlen, List.range_eq_range']
      apply any_congr'
      intro j hj
      rw [List.mem_range'] at hj
      rw [bad_eq h hc _ j (by omega)]
    rw [e2]
    rfl

theorem pat_fold {dt : Data} {dk : DK} (h : Rel dt dk) {cands : Array C4} {cs : List Cand}
    (hc : CandRel dk cands cs) (dual : Array (Array Nat)) : ∀ (l : List Nat)
    (pats : Array (Array Nat)) (st : List (List Nat) × Bool), pats.toList.map Array.toList = st.1 →
    (l.foldl (patStepM dt cands dual) pats).toList.map Array.toList =
        (l.foldl (patStepK dk (LL dual) cs) st).1 ∧
      (st.2 || l.any (patBadM dt cands dual)) = (l.foldl (patStepK dk (LL dual) cs) st).2
  | [], _, st, hp => ⟨hp, Bool.or_false _⟩
  | code :: l, pats, st, hp => by
    obtain ⟨s1, s2⟩ := pat_step h hc dual code pats st hp
    obtain ⟨r1, r2⟩ := pat_fold h hc dual l _ _ s1
    refine ⟨r1, ?_⟩
    rw [List.any_cons, ← Bool.or_assoc, s2, r2]
    rfl

theorem patterns_rel {dt : Data} {dk : DK} (h : Rel dt dk) {cands : Array C4} {cs : List Cand}
    (hc : CandRel dk cands cs) (dual : Array (Array Nat)) :
    ((List.range' 0 (3 ^ dual.size)).foldl (patStepM dt cands dual) #[]).toList.map Array.toList =
        (patternsK dk (LL dual) cs).1 ∧
      (List.range' 0 (3 ^ dual.size)).any (patBadM dt cands dual) = (patternsK dk (LL dual) cs).2 := by
  have := pat_fold h hc dual (List.range' 0 (3 ^ dual.size)) #[] ([], false) rfl
  rw [Bool.false_or] at this
  rw [patternsK_eq, length_LL, List.range_eq_range']
  exact this

end Certificates.GilmanCensusK

end
