module

public import Mathlib.Combinatorics.Quiver.Schreier
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.Certificates

abbrev SchreierLetter (j : ℕ) := Fin j × Bool

@[expose] def schreierLetterCode {j : ℕ} (a : SchreierLetter j) : ℤ :=
  if a.2 then (a.1.val + 1 : ℕ) else -((a.1.val + 1 : ℕ) : ℤ)

theorem schreierLetterCode_bounds {j : ℕ} (a : SchreierLetter j) :
    1 ≤ (schreierLetterCode a).natAbs ∧ (schreierLetterCode a).natAbs ≤ j := by
  rcases a with ⟨h, sign⟩
  cases sign <;> simp [schreierLetterCode] <;> omega

@[expose] def schreierWordValue {G : Type*} [Group G] {r : ℕ}
    (S : Fin r → G) (j : ℕ) (hj : j ≤ r) (w : List (SchreierLetter j)) : G :=
  Quiver.SchreierGraph.evalWord (fun h : Fin j => S ⟨h.val, h.isLt.trans_le hj⟩) w

theorem schreier_word_zero (w : List (SchreierLetter 0)) : w = [] := by
  cases w with
  | nil => rfl
  | cons a _ => exact Fin.elim0 a.1

theorem schreierWordValue_nil {G : Type*} [Group G] {r : ℕ}
    (S : Fin r → G) (j : ℕ) (hj : j ≤ r) :
    schreierWordValue S j hj [] = 1 := rfl

theorem schreierWordValue_cons_positive {G : Type*} [Group G] {r j : ℕ}
    (S : Fin r → G) (hj : j ≤ r) (a : Fin j) (w : List (SchreierLetter j)) :
    schreierWordValue S j hj ((a, true) :: w) =
      S ⟨a.val, a.isLt.trans_le hj⟩ * schreierWordValue S j hj w := rfl

theorem schreierWordValue_cons_negative {G : Type*} [Group G] {r j : ℕ}
    (S : Fin r → G) (hj : j ≤ r) (a : Fin j) (w : List (SchreierLetter j)) :
    schreierWordValue S j hj ((a, false) :: w) =
      (S ⟨a.val, a.isLt.trans_le hj⟩)⁻¹ * schreierWordValue S j hj w := rfl

@[expose] def schreierPermEq {n : ℕ} (g h : Equiv.Perm (Fin n)) : Bool :=
  (List.finRange n).all fun x => decide (g x = h x)

theorem schreierPermEq_eq_true_iff {n : ℕ} (g h : Equiv.Perm (Fin n)) :
    schreierPermEq g h = true ↔ g = h := by
  simp only [schreierPermEq, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro heq
    exact Equiv.ext fun x => heq x (List.mem_finRange x)
  · rintro rfl
    exact fun _ _ => rfl

structure RawSchreierDatum (n : ℕ) where
  degree_pos : 1 ≤ n
  originalCount : ℕ
  strongCount : ℕ
  baseCount : ℕ
  originalCount_le : originalCount ≤ strongCount
  original : Vector (Equiv.Perm (Fin n)) originalCount
  strong : Vector (Equiv.Perm (Fin n)) strongCount
  base : Vector (Fin n) baseCount
  base_distinct : base.toList.Nodup
  derivation : (j : Fin strongCount) → originalCount ≤ j.val →
    List (SchreierLetter j.val)

structure SchreierOrbitState (n : ℕ) where
  entries : List (Fin n × Equiv.Perm (Fin n))
  queue : List (Fin n)

namespace SchreierOrbitState

@[expose] def transversal? {n : ℕ} (q : SchreierOrbitState n) (x : Fin n) :
    Option (Equiv.Perm (Fin n)) := q.entries.lookup x

@[expose] def points {n : ℕ} (q : SchreierOrbitState n) : Set (Fin n) :=
  {x | (q.transversal? x).isSome = true}

@[expose] def initial {n : ℕ} (b : Fin n) : SchreierOrbitState n :=
  ⟨[(b, 1)], [b]⟩

@[expose] def discover {n : ℕ} (q : SchreierOrbitState n) (y : Fin n)
    (t : Equiv.Perm (Fin n)) : SchreierOrbitState n :=
  if (q.transversal? y).isSome then q
  else ⟨q.entries ++ [(y, t)], q.queue ++ [y]⟩

@[expose] def step {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (q : SchreierOrbitState n) : SchreierOrbitState n :=
  match q.queue with
  | [] => q
  | x :: pending =>
    let tx := (q.transversal? x).getD 1
    steps.foldl (fun state s => state.discover (s x) (s * tx))
      ⟨q.entries, pending⟩

@[expose] def run {n : ℕ} (steps : List (Equiv.Perm (Fin n))) :
    ℕ → SchreierOrbitState n → SchreierOrbitState n
  | 0, q => q
  | fuel + 1, q => run steps fuel (step steps q)

theorem initial_transversal {n : ℕ} (b : Fin n) :
    (initial b).transversal? b = some 1 := by
  simp [initial, transversal?]

theorem discover_of_assigned {n : ℕ} (q : SchreierOrbitState n) (y : Fin n)
    (t : Equiv.Perm (Fin n)) (hy : (q.transversal? y).isSome = true) :
    q.discover y t = q := by
  simp [discover, hy]

theorem discover_of_unassigned {n : ℕ} (q : SchreierOrbitState n) (y : Fin n)
    (t : Equiv.Perm (Fin n)) (hy : q.transversal? y = none) :
    q.discover y t = ⟨q.entries ++ [(y, t)], q.queue ++ [y]⟩ := by
  simp [discover, hy]

theorem discover_preserves_transversal {n : ℕ} (q : SchreierOrbitState n)
    (x y : Fin n) (u t : Equiv.Perm (Fin n)) (hx : q.transversal? x = some u) :
    (q.discover y t).transversal? x = some u := by
  change q.entries.lookup x = some u at hx
  unfold discover
  split
  · exact hx
  · simp only [transversal?, List.lookup_append, hx, Option.some_or]

theorem discover_assigns_transversal {n : ℕ} (q : SchreierOrbitState n)
    (y : Fin n) (t : Equiv.Perm (Fin n)) (hy : q.transversal? y = none) :
    (q.discover y t).transversal? y = some t := by
  change q.entries.lookup y = none at hy
  simp [discover, transversal?, hy, List.lookup_append]

theorem discoveries_preserve_transversal {n : ℕ}
    (steps : List (Equiv.Perm (Fin n))) (q : SchreierOrbitState n)
    (x y : Fin n) (u tx : Equiv.Perm (Fin n)) (hx : q.transversal? x = some u) :
    (steps.foldl (fun state s => state.discover (s y) (s * tx)) q).transversal? x = some u := by
  induction steps generalizing q with
  | nil => exact hx
  | cons s steps ih =>
    exact ih (q.discover (s y) (s * tx))
      (discover_preserves_transversal q x (s y) u (s * tx) hx)

theorem step_preserves_transversal {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (q : SchreierOrbitState n) (x : Fin n) (u : Equiv.Perm (Fin n))
    (hx : q.transversal? x = some u) : (step steps q).transversal? x = some u := by
  unfold step
  split
  · exact hx
  · exact discoveries_preserve_transversal steps _ x _ u _ hx

theorem run_preserves_transversal {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (fuel : ℕ) (q : SchreierOrbitState n) (x : Fin n) (u : Equiv.Perm (Fin n))
    (hx : q.transversal? x = some u) : (run steps fuel q).transversal? x = some u := by
  induction fuel generalizing q with
  | zero => exact hx
  | succ fuel ih => exact ih (step steps q) (step_preserves_transversal steps q x u hx)

theorem run_initial_root {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (fuel : ℕ) (b : Fin n) : (run steps fuel (initial b)).transversal? b = some 1 :=
  run_preserves_transversal steps fuel (initial b) b 1 (initial_transversal b)

theorem step_of_queue_empty {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (q : SchreierOrbitState n) (hq : q.queue = []) : step steps q = q := by
  simp [step, hq]

theorem run_zero {n : ℕ} (steps : List (Equiv.Perm (Fin n))) (q : SchreierOrbitState n) :
    run steps 0 q = q := rfl

theorem run_succ {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (fuel : ℕ) (q : SchreierOrbitState n) :
    run steps (fuel + 1) q = run steps fuel (step steps q) := rfl

end SchreierOrbitState

@[expose] def schreierSiftResidual {n : ℕ} :
    List (Fin n × SchreierOrbitState n) → Equiv.Perm (Fin n) →
      Option (Equiv.Perm (Fin n))
  | [], h => some h
  | (b, q) :: levels, h =>
    match q.transversal? (h b) with
    | none => none
    | some t => schreierSiftResidual levels (t⁻¹ * h)

@[expose] def schreierSiftSucceeds {n : ℕ}
    (levels : List (Fin n × SchreierOrbitState n)) (h : Equiv.Perm (Fin n)) : Bool :=
  match schreierSiftResidual levels h with
  | none => false
  | some residual => schreierPermEq residual 1

theorem schreierSiftSucceeds_eq_true_iff {n : ℕ}
    (levels : List (Fin n × SchreierOrbitState n)) (h : Equiv.Perm (Fin n)) :
    schreierSiftSucceeds levels h = true ↔ schreierSiftResidual levels h = some 1 := by
  unfold schreierSiftSucceeds
  cases he : schreierSiftResidual levels h with
  | none => simp
  | some residual => simp [schreierPermEq_eq_true_iff]

theorem schreierSiftSucceeds_nil {n : ℕ} (h : Equiv.Perm (Fin n)) :
    schreierSiftSucceeds [] h = true ↔ h = 1 :=
  schreierPermEq_eq_true_iff h 1

theorem schreierSiftSucceeds_eq_false_iff {n : ℕ}
    (levels : List (Fin n × SchreierOrbitState n)) (h : Equiv.Perm (Fin n)) :
    schreierSiftSucceeds levels h = false ↔ schreierSiftResidual levels h ≠ some 1 := by
  rw [Bool.eq_false_iff]
  exact not_congr (schreierSiftSucceeds_eq_true_iff levels h)

theorem schreierSiftResidual_unavailable {n : ℕ} (b : Fin n)
    (q : SchreierOrbitState n) (levels : List (Fin n × SchreierOrbitState n))
    (h : Equiv.Perm (Fin n)) (hu : q.transversal? (h b) = none) :
    schreierSiftResidual ((b, q) :: levels) h = none := by
  simp [schreierSiftResidual, hu]

theorem schreierSiftResidual_available {n : ℕ} (b : Fin n)
    (q : SchreierOrbitState n) (levels : List (Fin n × SchreierOrbitState n))
    (h t : Equiv.Perm (Fin n)) (ht : q.transversal? (h b) = some t) :
    schreierSiftResidual ((b, q) :: levels) h = schreierSiftResidual levels (t⁻¹ * h) := by
  simp [schreierSiftResidual, ht]

namespace RawSchreierDatum

@[expose] def levelGenerators {n : ℕ} (Q : RawSchreierDatum n) (i : ℕ) :
    List (Equiv.Perm (Fin n)) :=
  Q.strong.toList.filter fun s =>
    (Q.base.toList.take i).all fun b => decide (s b = b)

@[expose] def levelSteps {n : ℕ} (Q : RawSchreierDatum n) (i : ℕ) :
    List (Equiv.Perm (Fin n)) :=
  Q.levelGenerators i ++ (Q.levelGenerators i).map fun s => s⁻¹

theorem mem_levelGenerators_iff {n : ℕ} (Q : RawSchreierDatum n) (i : ℕ)
    (s : Equiv.Perm (Fin n)) :
    s ∈ Q.levelGenerators i ↔ s ∈ Q.strong.toList ∧
      ∀ b ∈ Q.base.toList.take i, s b = b := by
  simp [levelGenerators, List.all_eq_true]

theorem levelGenerators_zero {n : ℕ} (Q : RawSchreierDatum n) :
    Q.levelGenerators 0 = Q.strong.toList := by
  simp [levelGenerators]

@[expose] def orbitSearch {n : ℕ} (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    SchreierOrbitState n :=
  SchreierOrbitState.run (Q.levelSteps i.val) n
    (SchreierOrbitState.initial (Q.base.get i))

@[expose] def orbitTables {n : ℕ} (Q : RawSchreierDatum n) :
    Vector (SchreierOrbitState n) Q.baseCount := Vector.ofFn Q.orbitSearch

theorem orbitTables_get {n : ℕ} (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    Q.orbitTables.get i = Q.orbitSearch i := by
  simp [orbitTables, Vector.get]
  congr 1

@[expose] def siftLevels {n : ℕ} (Q : RawSchreierDatum n)
    (tables : Vector (SchreierOrbitState n) Q.baseCount) (i : ℕ) :
    List (Fin n × SchreierOrbitState n) :=
  ((List.finRange Q.baseCount).drop i).map fun j => (Q.base.get j, tables.get j)

@[expose] def sift {n : ℕ} (Q : RawSchreierDatum n) (h : Equiv.Perm (Fin n))
    (i : ℕ) : Bool :=
  schreierSiftSucceeds (Q.siftLevels Q.orbitTables i) h

theorem sift_terminal {n : ℕ} (Q : RawSchreierDatum n) (h : Equiv.Perm (Fin n)) :
    Q.sift h Q.baseCount = true ↔ h = 1 := by
  have hdrop : (List.finRange Q.baseCount).drop Q.baseCount = [] := by
    exact List.drop_eq_nil_iff.2 (by simp)
  simpa only [sift, siftLevels, hdrop, List.map_nil] using schreierSiftSucceeds_nil h

theorem sift_empty_base {n : ℕ} (Q : RawSchreierDatum n)
    (hbase : Q.baseCount = 0) (h : Equiv.Perm (Fin n)) :
    Q.sift h 0 = true ↔ h = 1 := by
  simpa only [hbase] using Q.sift_terminal h

@[expose] def orbitPoints {n : ℕ} (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    Set (Fin n) := (Q.orbitSearch i).points

@[expose] def transversal? {n : ℕ} (Q : RawSchreierDatum n)
    (i : Fin Q.baseCount) (x : Fin n) : Option (Equiv.Perm (Fin n)) :=
  (Q.orbitSearch i).transversal? x

theorem transversal_root {n : ℕ} (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    Q.transversal? i (Q.base.get i) = some 1 :=
  SchreierOrbitState.run_initial_root (Q.levelSteps i.val) n (Q.base.get i)

@[expose] def derivationValue {n : ℕ} (Q : RawSchreierDatum n)
    (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val) : Equiv.Perm (Fin n) :=
  schreierWordValue Q.strong.get j.val (Nat.le_of_lt j.isLt) (Q.derivation j hj)

@[expose] def check {n : ℕ} (Q : RawSchreierDatum n) : Bool :=
  let initialOK := (List.finRange Q.originalCount).all fun j =>
    schreierPermEq (Q.strong.get (Fin.castLE Q.originalCount_le j)) (Q.original.get j)
  let wordsOK := (List.finRange Q.strongCount).all fun j =>
    if hj : Q.originalCount ≤ j.val then
      schreierPermEq (Q.strong.get j) (Q.derivationValue j hj)
    else true
  let terminalOK := (Q.levelGenerators Q.baseCount).all fun s => schreierPermEq s 1
  let tables := Q.orbitTables
  let schreierOK := (List.finRange Q.baseCount).all fun i =>
    let q := tables.get i
    (List.finRange n).all fun x =>
      match q.transversal? x with
      | none => true
      | some tx => (Q.levelSteps i.val).all fun s =>
        match q.transversal? (s x) with
        | none => false
        | some ty => schreierSiftSucceeds (Q.siftLevels tables (i.val + 1)) (ty⁻¹ * s * tx)
  initialOK && wordsOK && terminalOK && schreierOK

private theorem finite_schreier_row_check {n : ℕ} (q : SchreierOrbitState n)
    (steps : List (Equiv.Perm (Fin n))) (levels : List (Fin n × SchreierOrbitState n))
    (x : Fin n) :
    (match q.transversal? x with
      | none => true
      | some tx => steps.all fun s =>
        match q.transversal? (s x) with
        | none => false
        | some ty => schreierSiftSucceeds levels (ty⁻¹ * s * tx)) = true ↔
      ∀ tx, q.transversal? x = some tx → ∀ s ∈ steps, ∃ ty,
        q.transversal? (s x) = some ty ∧ schreierSiftSucceeds levels (ty⁻¹ * s * tx) = true := by
  cases hx : q.transversal? x with
  | none => simp
  | some tx =>
    simp only [List.all_eq_true, Option.some.injEq, forall_eq']
    apply forall_congr'
    intro s
    apply forall_congr'
    intro _
    cases q.transversal? (s x) <;> simp

theorem check_eq_true_iff {n : ℕ} (Q : RawSchreierDatum n) :
    Q.check = true ↔
      (∀ j : Fin Q.originalCount,
        Q.strong.get (Fin.castLE Q.originalCount_le j) = Q.original.get j) ∧
      (∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
        Q.strong.get j = Q.derivationValue j hj) ∧
      (∀ s ∈ Q.levelGenerators Q.baseCount, s = 1) ∧
      (∀ (i : Fin Q.baseCount) (x : Fin n) (tx : Equiv.Perm (Fin n)),
        (Q.orbitTables.get i).transversal? x = some tx →
        ∀ s ∈ Q.levelSteps i.val, ∃ ty : Equiv.Perm (Fin n),
          (Q.orbitTables.get i).transversal? (s x) = some ty ∧
          schreierSiftSucceeds (Q.siftLevels Q.orbitTables (i.val + 1)) (ty⁻¹ * s * tx) = true) := by
  simp [check, List.all_eq_true, schreierPermEq_eq_true_iff,
    finite_schreier_row_check, and_assoc]

end RawSchreierDatum

@[expose] def ValidSchreier {n : ℕ} (Q : RawSchreierDatum n) : Prop := Q.check = true

instance instDecidableValidSchreier {n : ℕ} (Q : RawSchreierDatum n) :
    Decidable (ValidSchreier Q) :=
  inferInstanceAs (Decidable (Q.check = true))

theorem validSchreier_iff {n : ℕ} (Q : RawSchreierDatum n) :
    ValidSchreier Q ↔
      (∀ j : Fin Q.originalCount,
        Q.strong.get (Fin.castLE Q.originalCount_le j) = Q.original.get j) ∧
      (∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
        Q.strong.get j = Q.derivationValue j hj) ∧
      (∀ s ∈ Q.levelGenerators Q.baseCount, s = 1) ∧
      (∀ (i : Fin Q.baseCount) (x : Fin n) (tx : Equiv.Perm (Fin n)),
        (Q.orbitSearch i).transversal? x = some tx →
        ∀ s ∈ Q.levelSteps i.val, ∃ ty : Equiv.Perm (Fin n),
          (Q.orbitSearch i).transversal? (s x) = some ty ∧
          schreierSiftSucceeds (Q.siftLevels Q.orbitTables (i.val + 1)) (ty⁻¹ * s * tx) = true) := by
  simpa only [ValidSchreier, RawSchreierDatum.orbitTables_get] using Q.check_eq_true_iff

end CFSG.Certificates
