module

public import Batteries.Data.Vector.Lemmas
public import CFSG.Certificates.SchreierChainData

public section

namespace CFSG.Certificates

structure LiftedOrbitState (n : ℕ) (K : Type*) where
  entries : List (Fin n × (Equiv.Perm (Fin n) × K))
  queue : List (Fin n)

namespace LiftedOrbitState

variable {n : ℕ} {K : Type*}

@[expose] def transversal? (q : LiftedOrbitState n K) (x : Fin n) :
    Option (Equiv.Perm (Fin n) × K) := q.entries.lookup x

@[expose] def toPerm (q : LiftedOrbitState n K) : SchreierOrbitState n :=
  ⟨q.entries.map fun e => (e.1, e.2.1), q.queue⟩

theorem lookup_map_snd {α β γ : Type*} [DecidableEq α] (f : β → γ) (l : List (α × β)) (a : α) :
    (l.map fun e => (e.1, f e.2)).lookup a = (l.lookup a).map f := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k, b⟩ := e
    by_cases h : a = k
    · subst h
      simp [List.lookup]
    · have hk : (a == k) = false := beq_eq_false_iff_ne.2 h
      simp [List.lookup, hk, ih]

theorem toPerm_transversal? (q : LiftedOrbitState n K) (x : Fin n) :
    q.toPerm.transversal? x = (q.transversal? x).map Prod.fst :=
  lookup_map_snd Prod.fst q.entries x

@[expose] def discover (q : LiftedOrbitState n K) (y : Fin n)
    (t : Equiv.Perm (Fin n) × K) : LiftedOrbitState n K :=
  if (q.transversal? y).isSome then q
  else ⟨q.entries ++ [(y, t)], q.queue ++ [y]⟩

theorem toPerm_discover (q : LiftedOrbitState n K) (y : Fin n) (t : Equiv.Perm (Fin n) × K) :
    (q.discover y t).toPerm = q.toPerm.discover y t.1 := by
  unfold discover SchreierOrbitState.discover
  rw [toPerm_transversal?, Option.isSome_map]
  split <;> simp [toPerm]

variable [Group K]

@[expose] def initial (b : Fin n) : LiftedOrbitState n K := ⟨[(b, 1)], [b]⟩

@[expose] def step (steps : List (Equiv.Perm (Fin n) × K)) (q : LiftedOrbitState n K) :
    LiftedOrbitState n K :=
  match q.queue with
  | [] => q
  | x :: pending =>
    let tx := (q.transversal? x).getD 1
    steps.foldl (fun state s => state.discover (s.1 x) (s * tx)) ⟨q.entries, pending⟩

@[expose] def run (steps : List (Equiv.Perm (Fin n) × K)) :
    ℕ → LiftedOrbitState n K → LiftedOrbitState n K
  | 0, q => q
  | fuel + 1, q => run steps fuel (step steps q)

theorem toPerm_initial (b : Fin n) :
    (initial b : LiftedOrbitState n K).toPerm = SchreierOrbitState.initial b := rfl

theorem toPerm_foldl (steps : List (Equiv.Perm (Fin n) × K)) (q : LiftedOrbitState n K)
    (x : Fin n) (tx : Equiv.Perm (Fin n) × K) :
    (steps.foldl (fun state s => state.discover (s.1 x) (s * tx)) q).toPerm =
      (steps.map Prod.fst).foldl
        (fun state (s : Equiv.Perm (Fin n)) => state.discover (s x) (s * tx.1)) q.toPerm := by
  induction steps generalizing q with
  | nil => rfl
  | cons s steps ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons, toPerm_discover]
    rfl

theorem toPerm_step (steps : List (Equiv.Perm (Fin n) × K)) (q : LiftedOrbitState n K) :
    (step steps q).toPerm = SchreierOrbitState.step (steps.map Prod.fst) q.toPerm := by
  unfold step SchreierOrbitState.step
  change _ = match q.queue with
    | [] => q.toPerm
    | x :: pending =>
      let tx := (q.toPerm.transversal? x).getD 1
      (steps.map Prod.fst).foldl
        (fun state (s : Equiv.Perm (Fin n)) => state.discover (s x) (s * tx))
        ⟨q.toPerm.entries, pending⟩
  cases q.queue with
  | nil => rfl
  | cons x pending =>
    simp only
    rw [toPerm_foldl, toPerm_transversal?]
    have hfst : ((q.transversal? x).getD 1).1 = ((q.transversal? x).map Prod.fst).getD 1 := by
      cases q.transversal? x <;> rfl
    rw [hfst]
    rfl

theorem toPerm_run (steps : List (Equiv.Perm (Fin n) × K)) (fuel : ℕ)
    (q : LiftedOrbitState n K) :
    (run steps fuel q).toPerm = SchreierOrbitState.run (steps.map Prod.fst) fuel q.toPerm := by
  induction fuel generalizing q with
  | zero => rfl
  | succ fuel ih => rw [run, SchreierOrbitState.run, ih, toPerm_step]

end LiftedOrbitState

@[expose] def liftSiftResidual {n : ℕ} {K : Type*} [Group K] (φ : K →* Equiv.Perm (Fin n)) :
    List (Fin n × LiftedOrbitState n K) → K → Option K
  | [], v => some v
  | (b, q) :: levels, v =>
    match q.transversal? (φ v b) with
    | none => none
    | some t => liftSiftResidual φ levels (t.2⁻¹ * v)

namespace RawSchreierDatum

variable {n : ℕ} {K : Type*} [Group K]

@[expose] def liftStep (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (j : Fin Q.strongCount) (earlier : Fin j.val → K) : K :=
  if hm : j.val < Q.originalCount then U.get ⟨j.val, hm⟩
  else schreierWordValue earlier j.val le_rfl (Q.derivation j (Nat.le_of_not_lt hm))

@[expose] def liftPrefix (Q : RawSchreierDatum n) (U : Vector K Q.originalCount) :
    (j : ℕ) → j ≤ Q.strongCount → Vector K j
  | 0, _ => #v[]
  | j + 1, hj =>
    let prev := Q.liftPrefix U j (Nat.le_of_succ_le hj)
    prev.push (Q.liftStep U ⟨j, hj⟩ prev.get)

@[expose] def lift (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (j : Fin Q.strongCount) : K :=
  (Q.liftPrefix U Q.strongCount le_rfl).get j

theorem liftPrefix_get (Q : RawSchreierDatum n) (U : Vector K Q.originalCount) (j : ℕ)
    (hj : j ≤ Q.strongCount) (l : Fin j) :
    (Q.liftPrefix U j hj).get l =
      Q.liftStep U ⟨l.val, l.isLt.trans_le hj⟩ (Q.liftPrefix U l.val (l.isLt.le.trans hj)).get := by
  induction j with
  | zero => exact Fin.elim0 l
  | succ j ih =>
    obtain ⟨l, hl⟩ := l
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl' | rfl
    · rw [liftPrefix, Vector.get_eq_getElem]
      simp only
      rw [Vector.getElem_push_lt hl']
      exact ih _ ⟨l, hl'⟩
    · rw [liftPrefix, Vector.get_eq_getElem]
      simp only
      rw [Vector.getElem_push_last]

theorem liftPrefix_get_eq_lift (Q : RawSchreierDatum n) (U : Vector K Q.originalCount) (j : ℕ)
    (hj : j ≤ Q.strongCount) (l : Fin j) :
    (Q.liftPrefix U j hj).get l = Q.lift U ⟨l.val, l.isLt.trans_le hj⟩ := by
  rw [lift, liftPrefix_get, liftPrefix_get]

theorem lift_eq_liftStep (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (j : Fin Q.strongCount) :
    Q.lift U j = Q.liftStep U j fun l => Q.lift U ⟨l.val, l.isLt.trans j.isLt⟩ := by
  rw [lift, liftPrefix_get]
  congr 1
  funext l
  exact Q.liftPrefix_get_eq_lift U j.val _ l

theorem lift_of_lt (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (j : Fin Q.strongCount) (hm : j.val < Q.originalCount) :
    Q.lift U j = U.get ⟨j.val, hm⟩ := by
  rw [lift_eq_liftStep, liftStep, dite_eq_left hm]

theorem lift_castLE (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (j : Fin Q.originalCount) : Q.lift U (Fin.castLE Q.originalCount_le j) = U.get j :=
  Q.lift_of_lt U _ j.isLt

theorem lift_of_le (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (j : Fin Q.strongCount) (hm : Q.originalCount ≤ j.val) :
    Q.lift U j = schreierWordValue (Q.lift U) j.val (Nat.le_of_lt j.isLt) (Q.derivation j hm) := by
  rw [lift_eq_liftStep, liftStep, dite_eq_right (Nat.not_lt.2 hm)]
  rfl

@[expose] def levelIndices (Q : RawSchreierDatum n) (i : ℕ) : List (Fin Q.strongCount) :=
  (List.finRange Q.strongCount).filter fun j =>
    (Q.base.toList.take i).all fun b => decide (Q.strong.get j b = b)

theorem mem_levelIndices_iff (Q : RawSchreierDatum n) (i : ℕ) (j : Fin Q.strongCount) :
    j ∈ Q.levelIndices i ↔ ∀ b ∈ Q.base.toList.take i, Q.strong.get j b = b := by
  simp [levelIndices, List.all_eq_true]

theorem strong_toList_eq_map (Q : RawSchreierDatum n) :
    Q.strong.toList = (List.finRange Q.strongCount).map Q.strong.get := by
  apply List.ext_getElem <;> simp [Vector.get]

theorem levelIndices_map_strong (Q : RawSchreierDatum n) (i : ℕ) :
    (Q.levelIndices i).map Q.strong.get = Q.levelGenerators i := by
  rw [levelGenerators, strong_toList_eq_map, List.filter_map]
  rfl

@[expose] def liftedLevelGenerators (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : ℕ) : List K :=
  (Q.levelIndices i).map (Q.lift U)

@[expose] def liftedLevelSteps (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : ℕ) : List (Equiv.Perm (Fin n) × K) :=
  let forward := (Q.levelIndices i).map fun j => (Q.strong.get j, Q.lift U j)
  forward ++ forward.map fun p => p⁻¹

theorem liftedLevelSteps_map_fst (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : ℕ) : (Q.liftedLevelSteps U i).map Prod.fst = Q.levelSteps i := by
  simp only [liftedLevelSteps, levelSteps, List.map_append, List.map_map,
    ← levelIndices_map_strong]
  rfl

@[expose] def liftedOrbitSearch (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) : LiftedOrbitState n K :=
  LiftedOrbitState.run (Q.liftedLevelSteps U i.val) n (LiftedOrbitState.initial (Q.base.get i))

theorem liftedOrbitSearch_toPerm (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) : (Q.liftedOrbitSearch U i).toPerm = Q.orbitSearch i := by
  rw [liftedOrbitSearch, LiftedOrbitState.toPerm_run, LiftedOrbitState.toPerm_initial,
    liftedLevelSteps_map_fst]
  rfl

@[expose] def liftedOrbitTables (Q : RawSchreierDatum n) (U : Vector K Q.originalCount) :
    Vector (LiftedOrbitState n K) Q.baseCount :=
  Vector.ofFn (Q.liftedOrbitSearch U)

theorem liftedOrbitTables_get (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) : (Q.liftedOrbitTables U).get i = Q.liftedOrbitSearch U i :=
  Vector.get_ofFn _ i

@[expose] def liftedTransversal? (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) (x : Fin n) : Option K :=
  ((Q.liftedOrbitSearch U i).transversal? x).map Prod.snd

theorem transversal?_eq_map_fst (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) (x : Fin n) :
    Q.transversal? i x = ((Q.liftedOrbitSearch U i).transversal? x).map Prod.fst := by
  rw [transversal?, ← Q.liftedOrbitSearch_toPerm U i, LiftedOrbitState.toPerm_transversal?]

theorem liftedTransversal?_isSome_iff (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) (x : Fin n) :
    (Q.liftedTransversal? U i x).isSome = true ↔ x ∈ Q.orbitPoints i := by
  change _ ↔ (Q.transversal? i x).isSome = true
  rw [liftedTransversal?, Q.transversal?_eq_map_fst U i x, Option.isSome_map, Option.isSome_map]

@[expose] def liftedSiftLevels (Q : RawSchreierDatum n)
    (tables : Vector (LiftedOrbitState n K) Q.baseCount) (i : ℕ) :
    List (Fin n × LiftedOrbitState n K) :=
  ((List.finRange Q.baseCount).drop i).map fun j => (Q.base.get j, tables.get j)

end RawSchreierDatum

variable {n : ℕ} {K : Type*} [Group K]

@[expose] def LiftSift (Q : RawSchreierDatum n) (φ : K →* Equiv.Perm (Fin n))
    (U : Vector K Q.originalCount) (v : K) (i : ℕ) : Prop :=
  liftSiftResidual φ (Q.liftedSiftLevels (Q.liftedOrbitTables U) i) v = some 1

instance instDecidableLiftSift [DecidableEq K] (Q : RawSchreierDatum n)
    (φ : K →* Equiv.Perm (Fin n)) (U : Vector K Q.originalCount) (v : K) (i : ℕ) :
    Decidable (LiftSift Q φ U v i) :=
  inferInstanceAs (Decidable (_ = some 1))

structure ValidLiftedSchreier (Q : RawSchreierDatum n) (φ : K →* Equiv.Perm (Fin n))
    (U : Vector K Q.originalCount) : Prop where
  valid : ValidSchreier Q
  original_image : ∀ j : Fin Q.originalCount, φ (U.get j) = Q.original.get j
  terminal : ∀ h ∈ Q.liftedLevelGenerators U Q.baseCount, h = 1
  schreier : ∀ (i : Fin Q.baseCount) (x : Fin n) (tx : K),
    Q.liftedTransversal? U i x = some tx → ∀ p ∈ Q.liftedLevelSteps U i.val,
      ∃ ty : K, Q.liftedTransversal? U i (p.1 x) = some ty ∧
        LiftSift Q φ U (ty⁻¹ * p.2 * tx) (i.val + 1)

theorem validLiftedSchreier_iff (Q : RawSchreierDatum n) (φ : K →* Equiv.Perm (Fin n))
    (U : Vector K Q.originalCount) :
    ValidLiftedSchreier Q φ U ↔ ValidSchreier Q ∧
      (∀ j : Fin Q.originalCount, φ (U.get j) = Q.original.get j) ∧
      (∀ h ∈ Q.liftedLevelGenerators U Q.baseCount, h = 1) ∧
      ∀ (i : Fin Q.baseCount) (x : Fin n) (tx : K), Q.liftedTransversal? U i x = some tx →
        ∀ p ∈ Q.liftedLevelSteps U i.val, ∃ ty : K, Q.liftedTransversal? U i (p.1 x) = some ty ∧
          LiftSift Q φ U (ty⁻¹ * p.2 * tx) (i.val + 1) :=
  ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

theorem validLiftedSchreier_iff_bounded (Q : RawSchreierDatum n) (φ : K →* Equiv.Perm (Fin n))
    (U : Vector K Q.originalCount) :
    ValidLiftedSchreier Q φ U ↔ ValidSchreier Q ∧
      (∀ j : Fin Q.originalCount, schreierPermEq (φ (U.get j)) (Q.original.get j) = true) ∧
      (∀ h ∈ Q.liftedLevelGenerators U Q.baseCount, h = 1) ∧
      ∀ (i : Fin Q.baseCount) (x : Fin n), ∀ tx ∈ Q.liftedTransversal? U i x,
        ∀ p ∈ Q.liftedLevelSteps U i.val, ∃ ty ∈ Q.liftedTransversal? U i (p.1 x),
          LiftSift Q φ U (ty⁻¹ * p.2 * tx) (i.val + 1) := by
  simp only [schreierPermEq_eq_true_iff]
  exact validLiftedSchreier_iff Q φ U

instance instDecidableValidLiftedSchreier [DecidableEq K] (Q : RawSchreierDatum n)
    (φ : K →* Equiv.Perm (Fin n)) (U : Vector K Q.originalCount) :
    Decidable (ValidLiftedSchreier Q φ U) :=
  decidable_of_iff _ (validLiftedSchreier_iff_bounded Q φ U).symm

end CFSG.Certificates
