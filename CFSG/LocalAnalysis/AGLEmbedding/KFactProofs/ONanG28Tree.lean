module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Check
public import Std.Data.HashSet.Lemmas
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4.Item434G28

@[expose] def invDiag (u : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 36) fun t => if t.val % 7 = 0 then u[t.val]! ^^^ 1 else u[t.val]!

@[expose] def canonCode (u : Array ℕ) : Array ℕ := if u[0]! % 2 = 0 then u else invDiag u

@[expose] def conjCode (g gi c : Array ℕ) : Array ℕ := mulCode (mulCode g c) gi

structure TreeData where
  R : ℕ
  N : ℕ
  roots : Array (Array ℕ)
  gens : Array (Array ℕ)
  ginvs : Array (Array ℕ)
  par : ℕ → ℕ
  sym : ℕ → ℕ

namespace TreeData

@[expose] def step (D : TreeData) (acc : Array (Array ℕ × ℕ)) (n : ℕ) : Array ℕ × ℕ :=
  if n < D.R then (D.roots[n]!, n) else
    (canonCode (conjCode D.gens[D.sym n]! D.ginvs[D.sym n]! (acc[D.par n]!).1), (acc[D.par n]!).2)

@[expose] def pre (D : TreeData) (m : ℕ) : Array (Array ℕ × ℕ) :=
  (List.range m).foldl (fun acc n => acc.push (D.step acc n)) #[]

@[expose] def build (D : TreeData) : Array (Array ℕ × ℕ) := D.pre D.N

@[expose] def ok (D : TreeData) : Bool :=
  (List.range D.N).all fun n => D.R ≤ n → (D.par n < n && D.sym n < D.gens.size)

theorem pre_succ (D : TreeData) (m : ℕ) :
    D.pre (m + 1) = (D.pre m).push (D.step (D.pre m) m) := by
  simp [pre, List.range_succ, List.foldl_append]

theorem pre_size (D : TreeData) (m : ℕ) : (D.pre m).size = m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pre_succ, Array.size_push, ih]

theorem pre_getElem_stable (D : TreeData) {m i : ℕ} (hi : i < m) :
    (D.pre m)[i]! = (D.pre (i + 1))[i]! := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge i m with h | h
    · rw [pre_succ, getElem!_pos _ i (by simp [pre_size]; omega), Array.getElem_push_lt
        (by rw [pre_size]; exact h), ← getElem!_pos _ i (by rw [pre_size]; exact h)]
      exact ih h
    · have : i = m := by omega
      subst this
      rfl

theorem pre_getElem_self (D : TreeData) (i : ℕ) :
    (D.pre (i + 1))[i]! = D.step (D.pre i) i := by
  rw [pre_succ, getElem!_pos _ i (by simp [pre_size])]
  simp only [Array.getElem_push, pre_size, lt_irrefl, ↓reduceDIte]

theorem build_spec (D : TreeData) (h : D.ok = true) :
    D.build.size = D.N ∧ ∀ n < D.N,
      (n < D.R → D.build[n]! = (D.roots[n]!, n)) ∧
      (D.R ≤ n → D.par n < n ∧ D.sym n < D.gens.size ∧
        D.build[n]! = (canonCode (conjCode D.gens[D.sym n]! D.ginvs[D.sym n]!
          (D.build[D.par n]!).1), (D.build[D.par n]!).2)) := by
  simp only [ok, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨pre_size D D.N, fun n hn => ⟨fun hnR => ?_, fun hnR => ?_⟩⟩
  · have := pre_getElem_stable D hn
    rw [build, this, pre_getElem_self, step, ite_eq_left hnR]
  · obtain ⟨hp, hs⟩ := h n hn hnR
    refine ⟨hp, hs, ?_⟩
    have h1 : D.build[n]! = D.step (D.pre n) n := by
      rw [build, pre_getElem_stable D hn, pre_getElem_self]
    have h2 : (D.pre n)[D.par n]! = D.build[D.par n]! := by
      rw [build, pre_getElem_stable D (lt_trans hp hn), pre_getElem_stable D hp]
    rw [h1, step, ite_eq_right (by omega), h2]

end TreeData

@[expose] def codeKey (u : Array ℕ) : UInt64 × UInt64 :=
  ((List.range 18).foldl (fun acc i => (acc <<< 3) ||| (u[i]!).toUInt64) 0,
    (List.range 18).foldl (fun acc i => (acc <<< 3) ||| (u[18 + i]!).toUInt64) 0)

@[expose] def distinctStep (st : Std.HashSet (UInt64 × UInt64) × Bool) (c : Array ℕ) :
    Std.HashSet (UInt64 × UInt64) × Bool :=
  match st with
  | (s, b) =>
    let k := codeKey c
    let seen := s.contains k
    (s.insert k, b && !seen)

@[expose] def distinctOK (l : List (Array ℕ)) : Bool := (l.foldl distinctStep (∅, true)).2

theorem distinct_inv (l : List (Array ℕ)) (s : Std.HashSet (UInt64 × UInt64)) (b : Bool) :
    (l.foldl distinctStep (s, b)).2 = true → b = true ∧ (l.map codeKey).Nodup ∧
      ∀ u ∈ l, s.contains (codeKey u) = false := by
  induction l generalizing s b with
  | nil => intro h; exact ⟨h, List.nodup_nil, by simp⟩
  | cons u l ih =>
    intro h
    simp only [List.foldl_cons, distinctStep] at h
    obtain ⟨hb, hnd, hall⟩ := ih _ _ h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
    refine ⟨hb.1, ?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, hnd⟩
      obtain ⟨u', hu', hkey⟩ := List.mem_map.mp hmem
      have := hall u' hu'
      rw [Std.HashSet.contains_insert] at this
      simp [hkey] at this
    · intro u' hu'
      rcases List.mem_cons.mp hu' with rfl | hu'
      · exact hb.2
      · have := hall u' hu'
        rw [Std.HashSet.contains_insert] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.2

theorem distinctOK_spec {l : List (Array ℕ)} (h : distinctOK l = true) :
    ∀ i < l.length, ∀ j < l.length, l[i]! = l[j]! → i = j := by
  obtain ⟨-, hnd, -⟩ := distinct_inv l ∅ true h
  intro i hi j hj hij
  have hi' : i < (l.map codeKey).length := by simpa using hi
  have hj' : j < (l.map codeKey).length := by simpa using hj
  have : (l.map codeKey)[i] = (l.map codeKey)[j] := by
    simp only [List.getElem_map]
    rw [getElem!_pos l i hi, getElem!_pos l j hj] at hij
    rw [hij]
  exact (List.Nodup.getElem_inj_iff hnd).mp this

end CFSG.AGLEmbedding.KFactProofs.G28
