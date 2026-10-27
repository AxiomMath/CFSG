module

public import CFSG.Certificates.LiftedSchreierData
public import CFSG.Certificates.SchreierChainOrderGenerators

public section

namespace CFSG.Certificates

variable {n : ℕ} {K : Type*} [Group K]

namespace LiftedOrbitState

omit [Group K] in
theorem discover_entries (q : LiftedOrbitState n K) (y : Fin n) (t : Equiv.Perm (Fin n) × K) :
    ∃ rest, (q.discover y t).entries = q.entries ++ rest := by
  unfold discover
  split
  · exact ⟨[], (List.append_nil _).symm⟩
  · exact ⟨[(y, t)], rfl⟩

theorem foldl_entries (steps : List (Equiv.Perm (Fin n) × K)) (q : LiftedOrbitState n K)
    (x : Fin n) (tx : Equiv.Perm (Fin n) × K) :
    ∃ rest, (steps.foldl (fun state s => state.discover (s.1 x) (s * tx)) q).entries =
      q.entries ++ rest := by
  induction steps generalizing q with
  | nil => exact ⟨[], (List.append_nil _).symm⟩
  | cons s steps ih =>
    obtain ⟨r₁, h₁⟩ := discover_entries q (s.1 x) (s * tx)
    obtain ⟨r₂, h₂⟩ := ih (q.discover (s.1 x) (s * tx))
    exact ⟨r₁ ++ r₂, by rw [List.foldl_cons, h₂, h₁, List.append_assoc]⟩

theorem step_entries (steps : List (Equiv.Perm (Fin n) × K)) (q : LiftedOrbitState n K) :
    ∃ rest, (step steps q).entries = q.entries ++ rest := by
  unfold step
  split
  · exact ⟨[], (List.append_nil _).symm⟩
  · exact foldl_entries steps _ _ _

theorem run_entries (steps : List (Equiv.Perm (Fin n) × K)) (fuel : ℕ)
    (q : LiftedOrbitState n K) : ∃ rest, (run steps fuel q).entries = q.entries ++ rest := by
  induction fuel generalizing q with
  | zero => exact ⟨[], (List.append_nil _).symm⟩
  | succ fuel ih =>
    obtain ⟨r₁, h₁⟩ := step_entries steps q
    obtain ⟨r₂, h₂⟩ := ih (step steps q)
    exact ⟨r₁ ++ r₂, by rw [run, h₂, h₁, List.append_assoc]⟩

theorem run_initial_root (steps : List (Equiv.Perm (Fin n) × K)) (fuel : ℕ) (b : Fin n) :
    (run steps fuel (initial b)).transversal? b = some 1 := by
  obtain ⟨rest, h⟩ := run_entries steps fuel (initial b)
  rw [transversal?, h]
  simp [initial]

omit [Group K] in
theorem mem_entries_of_transversal (q : LiftedOrbitState n K) (x : Fin n)
    (t : Equiv.Perm (Fin n) × K) (ht : q.transversal? x = some t) : (x, t) ∈ q.entries := by
  obtain ⟨before, after, heq, _⟩ := List.lookup_eq_some_iff.1 ht
  simp [heq]

def EntriesIn (M : Subgroup (Equiv.Perm (Fin n) × K)) (q : LiftedOrbitState n K) : Prop :=
  ∀ e ∈ q.entries, e.2 ∈ M

theorem EntriesIn.lookup_getD_mem {M : Subgroup (Equiv.Perm (Fin n) × K)}
    {q : LiftedOrbitState n K} (hq : EntriesIn M q) (x : Fin n) :
    (q.transversal? x).getD 1 ∈ M := by
  cases hx : q.transversal? x with
  | none => exact M.one_mem
  | some t => exact hq (x, t) (mem_entries_of_transversal q x t hx)

theorem EntriesIn.discover {M : Subgroup (Equiv.Perm (Fin n) × K)} {q : LiftedOrbitState n K}
    (hq : EntriesIn M q) (y : Fin n) {t : Equiv.Perm (Fin n) × K} (ht : t ∈ M) :
    EntriesIn M (q.discover y t) := by
  unfold LiftedOrbitState.discover
  split
  · exact hq
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact hq e he
    · rw [List.mem_singleton.1 he]
      exact ht

theorem EntriesIn.foldl {M : Subgroup (Equiv.Perm (Fin n) × K)}
    {steps : List (Equiv.Perm (Fin n) × K)} (hsteps : ∀ s ∈ steps, s ∈ M)
    {q : LiftedOrbitState n K} (hq : EntriesIn M q) (x : Fin n)
    {tx : Equiv.Perm (Fin n) × K} (htx : tx ∈ M) :
    EntriesIn M (steps.foldl (fun state s => state.discover (s.1 x) (s * tx)) q) := by
  induction steps generalizing q with
  | nil => exact hq
  | cons s steps ih =>
    exact ih (fun u hu => hsteps u (List.mem_cons_of_mem s hu))
      (hq.discover (s.1 x) (M.mul_mem (hsteps s List.mem_cons_self) htx))

theorem EntriesIn.step {M : Subgroup (Equiv.Perm (Fin n) × K)}
    {steps : List (Equiv.Perm (Fin n) × K)} (hsteps : ∀ s ∈ steps, s ∈ M)
    {q : LiftedOrbitState n K} (hq : EntriesIn M q) :
    EntriesIn M (LiftedOrbitState.step steps q) := by
  unfold LiftedOrbitState.step
  cases q.queue with
  | nil => exact hq
  | cons x pending =>
    exact EntriesIn.foldl hsteps (q := ⟨q.entries, pending⟩) hq x (hq.lookup_getD_mem x)

theorem EntriesIn.run {M : Subgroup (Equiv.Perm (Fin n) × K)}
    {steps : List (Equiv.Perm (Fin n) × K)} (hsteps : ∀ s ∈ steps, s ∈ M) (fuel : ℕ)
    {q : LiftedOrbitState n K} (hq : EntriesIn M q) :
    EntriesIn M (LiftedOrbitState.run steps fuel q) := by
  induction fuel generalizing q with
  | zero => exact hq
  | succ fuel ih => exact ih (hq.step hsteps)

theorem run_initial_transversal_mem (M : Subgroup (Equiv.Perm (Fin n) × K))
    (steps : List (Equiv.Perm (Fin n) × K)) (hsteps : ∀ s ∈ steps, s ∈ M) (fuel : ℕ)
    (b x : Fin n) (t : Equiv.Perm (Fin n) × K)
    (ht : (run steps fuel (initial b)).transversal? x = some t) : t ∈ M := by
  have hinit : EntriesIn M (initial b : LiftedOrbitState n K) := by
    intro e he
    rw [List.mem_singleton.1 he]
    exact M.one_mem
  exact EntriesIn.run hsteps fuel hinit (x, t) (mem_entries_of_transversal _ x t ht)

end LiftedOrbitState

theorem liftSiftResidual_nil (φ : K →* Equiv.Perm (Fin n)) (v : K) :
    liftSiftResidual φ [] v = some v := rfl

theorem liftSiftResidual_unavailable (φ : K →* Equiv.Perm (Fin n)) (b : Fin n)
    (q : LiftedOrbitState n K) (levels : List (Fin n × LiftedOrbitState n K)) (v : K)
    (hu : q.transversal? (φ v b) = none) : liftSiftResidual φ ((b, q) :: levels) v = none := by
  simp [liftSiftResidual, hu]

theorem liftSiftResidual_available (φ : K →* Equiv.Perm (Fin n)) (b : Fin n)
    (q : LiftedOrbitState n K) (levels : List (Fin n × LiftedOrbitState n K)) (v : K)
    (t : Equiv.Perm (Fin n) × K) (ht : q.transversal? (φ v b) = some t) :
    liftSiftResidual φ ((b, q) :: levels) v = liftSiftResidual φ levels (t.2⁻¹ * v) := by
  simp [liftSiftResidual, ht]

theorem liftSiftResidual_mem_iff (φ : K →* Equiv.Perm (Fin n))
    (levels : List (Fin n × LiftedOrbitState n K)) (M : Subgroup K)
    (htrans : ∀ p ∈ levels, ∀ (x : Fin n) (t : Equiv.Perm (Fin n) × K),
      p.2.transversal? x = some t → t.2 ∈ M)
    (v r : K) (hr : liftSiftResidual φ levels v = some r) : v ∈ M ↔ r ∈ M := by
  induction levels generalizing v with
  | nil => rw [Option.some.inj hr]
  | cons p levels ih =>
    rcases p with ⟨b, q⟩
    cases ht : q.transversal? (φ v b) with
    | none => rw [liftSiftResidual_unavailable φ b q levels v ht] at hr; cases hr
    | some t =>
      rw [liftSiftResidual_available φ b q levels v t ht] at hr
      have htM := htrans (b, q) List.mem_cons_self (φ v b) t ht
      exact (M.mul_mem_cancel_left (M.inv_mem htM)).symm.trans
        (ih (fun p hp x u hu => htrans p (List.mem_cons_of_mem _ hp) x u hu) (t.2⁻¹ * v) hr)

theorem liftSiftResidual_mem (φ : K →* Equiv.Perm (Fin n))
    (levels : List (Fin n × LiftedOrbitState n K)) (M : Subgroup K)
    (htrans : ∀ p ∈ levels, ∀ (x : Fin n) (t : Equiv.Perm (Fin n) × K),
      p.2.transversal? x = some t → t.2 ∈ M)
    (v : K) (hv : liftSiftResidual φ levels v = some 1) : v ∈ M :=
  (liftSiftResidual_mem_iff φ levels M htrans v 1 hv).2 M.one_mem

namespace RawSchreierDatum

@[expose] def liftedOriginalSubgroup (Q : RawSchreierDatum n) (U : Vector K Q.originalCount) :
    Subgroup K :=
  Subgroup.closure {g | g ∈ U.toList}

@[expose] def liftedLevelSubgroup (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : ℕ) : Subgroup K :=
  Subgroup.closure {h | h ∈ Q.liftedLevelGenerators U i}

theorem mem_liftedLevelGenerators_iff (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : ℕ) (h : K) : h ∈ Q.liftedLevelGenerators U i ↔ ∃ j ∈ Q.levelIndices i, Q.lift U j = h :=
  List.mem_map

theorem lift_mem_liftedLevelSubgroup (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : ℕ) (j : Fin Q.strongCount) (hj : j ∈ Q.levelIndices i) :
    Q.lift U j ∈ Q.liftedLevelSubgroup U i :=
  Subgroup.subset_closure (List.mem_map_of_mem hj)

theorem mem_liftedLevelSteps_iff (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : ℕ) (p : Equiv.Perm (Fin n) × K) :
    p ∈ Q.liftedLevelSteps U i ↔ ∃ j ∈ Q.levelIndices i,
      p = (Q.strong.get j, Q.lift U j) ∨ p = (Q.strong.get j, Q.lift U j)⁻¹ := by
  simp only [liftedLevelSteps, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨_, ⟨j, hj, rfl⟩, rfl⟩)
    · exact ⟨j, hj, Or.inl rfl⟩
    · exact ⟨j, hj, Or.inr rfl⟩
  · rintro ⟨j, hj, rfl | rfl⟩
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr ⟨_, ⟨j, hj, rfl⟩, rfl⟩

theorem liftedLevelSteps_mem (Q : RawSchreierDatum n) (U : Vector K Q.originalCount) (i : ℕ)
    (M : Subgroup (Equiv.Perm (Fin n) × K))
    (hM : ∀ j ∈ Q.levelIndices i, (Q.strong.get j, Q.lift U j) ∈ M) :
    ∀ p ∈ Q.liftedLevelSteps U i, p ∈ M := by
  intro p hp
  obtain ⟨j, hj, rfl | rfl⟩ := (Q.mem_liftedLevelSteps_iff U i p).1 hp
  · exact hM j hj
  · exact M.inv_mem (hM j hj)

theorem liftedOrbitSearch_mem (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) (M : Subgroup (Equiv.Perm (Fin n) × K))
    (hM : ∀ j ∈ Q.levelIndices i.val, (Q.strong.get j, Q.lift U j) ∈ M) (x : Fin n)
    (p : Equiv.Perm (Fin n) × K) (hp : (Q.liftedOrbitSearch U i).transversal? x = some p) :
    p ∈ M :=
  LiftedOrbitState.run_initial_transversal_mem M _ (Q.liftedLevelSteps_mem U i.val M hM) n _ x
    p hp

theorem lifted_record_mem (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) (x : Fin n) (p : Equiv.Perm (Fin n) × K)
    (hp : (Q.liftedOrbitSearch U i).transversal? x = some p) :
    p.2 ∈ Q.liftedLevelSubgroup U i.val :=
  (Q.liftedOrbitSearch_mem U i ((⊤ : Subgroup (Equiv.Perm (Fin n))).prod
    (Q.liftedLevelSubgroup U i.val)) (fun j hj => ⟨Subgroup.mem_top _,
      Q.lift_mem_liftedLevelSubgroup U i.val j hj⟩) x p hp).2

theorem liftedTransversal?_eq_some_iff (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) (x : Fin n) (T : K) :
    Q.liftedTransversal? U i x = some T ↔
      ∃ t, (Q.liftedOrbitSearch U i).transversal? x = some (t, T) := by
  rw [liftedTransversal?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨t, T'⟩, hp, rfl⟩
    exact ⟨t, hp⟩
  · rintro ⟨t, hp⟩
    exact ⟨(t, T), hp, rfl⟩

theorem liftedTransversal_mem (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) (x : Fin n) (T : K) (hT : Q.liftedTransversal? U i x = some T) :
    T ∈ Q.liftedLevelSubgroup U i.val := by
  obtain ⟨t, hp⟩ := (Q.liftedTransversal?_eq_some_iff U i x T).1 hT
  exact Q.lifted_record_mem U i x (t, T) hp

theorem liftedTransversal_root (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) : Q.liftedTransversal? U i (Q.base.get i) = some 1 := by
  rw [liftedTransversal?, liftedOrbitSearch, LiftedOrbitState.run_initial_root]
  rfl

theorem transversal_of_lifted_record (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) (x : Fin n) (p : Equiv.Perm (Fin n) × K)
    (hp : (Q.liftedOrbitSearch U i).transversal? x = some p) : Q.transversal? i x = some p.1 := by
  rw [Q.transversal?_eq_map_fst U i x, hp]
  rfl

theorem exists_lifted_record (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i : Fin Q.baseCount) (x : Fin n) (t : Equiv.Perm (Fin n)) (ht : Q.transversal? i x = some t) :
    ∃ T, (Q.liftedOrbitSearch U i).transversal? x = some (t, T) := by
  rw [Q.transversal?_eq_map_fst U i x, Option.map_eq_some_iff] at ht
  obtain ⟨⟨t', T⟩, hp, rfl⟩ := ht
  exact ⟨T, hp⟩

theorem lifted_record_map (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (φ : K →* Equiv.Perm (Fin n)) (hlift : ∀ j, φ (Q.lift U j) = Q.strong.get j)
    (i : Fin Q.baseCount) (x : Fin n) (p : Equiv.Perm (Fin n) × K)
    (hp : (Q.liftedOrbitSearch U i).transversal? x = some p) : p.1 = φ p.2 :=
  Q.liftedOrbitSearch_mem U i ((MonoidHom.fst (Equiv.Perm (Fin n)) K).eqLocus
    (φ.comp (MonoidHom.snd (Equiv.Perm (Fin n)) K)))
    (fun j _ => show Q.strong.get j = φ (Q.lift U j) from (hlift j).symm) x p hp

theorem lift_mem_liftedOriginalSubgroup (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (j : Fin Q.strongCount) : Q.lift U j ∈ Q.liftedOriginalSubgroup U := by
  have all : ∀ a : ℕ, ∀ j : Fin Q.strongCount, j.val = a →
      Q.lift U j ∈ Q.liftedOriginalSubgroup U := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja
      by_cases hj : j.val < Q.originalCount
      · rw [Q.lift_of_lt U j hj]
        exact Subgroup.subset_closure (schreier_vector_get_mem_toList U _)
      · rw [Q.lift_of_le U j (Nat.le_of_not_lt hj)]
        apply schreierWordValue_mem_subgroup
        intro l
        exact ih l.val (by omega) _ rfl
  exact all j.val j rfl

theorem levelIndices_zero (Q : RawSchreierDatum n) :
    Q.levelIndices 0 = List.finRange Q.strongCount := by
  simp [levelIndices]

theorem liftedLevelSubgroup_zero (Q : RawSchreierDatum n) (U : Vector K Q.originalCount) :
    Q.liftedLevelSubgroup U 0 = Q.liftedOriginalSubgroup U := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro h hh
    obtain ⟨j, _, rfl⟩ := (Q.mem_liftedLevelGenerators_iff U 0 h).1 hh
    exact Q.lift_mem_liftedOriginalSubgroup U j
  · apply (Subgroup.closure_le _).2
    intro g hg
    obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get U g).1 hg
    rw [← Q.lift_castLE U j]
    exact Q.lift_mem_liftedLevelSubgroup U 0 _ (by simp [levelIndices_zero])

theorem levelIndices_subset (Q : RawSchreierDatum n) (i j : ℕ) (hij : i ≤ j) :
    Q.levelIndices j ⊆ Q.levelIndices i := by
  intro l hl
  rw [mem_levelIndices_iff] at hl ⊢
  exact fun b hb => hl b (List.take_subset_take_left Q.base.toList hij hb)

theorem liftedLevelSubgroup_antitone (Q : RawSchreierDatum n) (U : Vector K Q.originalCount)
    (i j : ℕ) (hij : i ≤ j) : Q.liftedLevelSubgroup U j ≤ Q.liftedLevelSubgroup U i := by
  apply (Subgroup.closure_le _).2
  intro h hh
  obtain ⟨l, hl, rfl⟩ := (Q.mem_liftedLevelGenerators_iff U j h).1 hh
  exact Q.lift_mem_liftedLevelSubgroup U i l (Q.levelIndices_subset i j hij hl)

omit [Group K] in
theorem mem_liftedSiftLevels_iff (Q : RawSchreierDatum n)
    (tables : Vector (LiftedOrbitState n K) Q.baseCount) (i : ℕ)
    (p : Fin n × LiftedOrbitState n K) :
    p ∈ Q.liftedSiftLevels tables i ↔
      ∃ j : Fin Q.baseCount, i ≤ j.val ∧ (Q.base.get j, tables.get j) = p := by
  simp only [liftedSiftLevels, List.mem_map, mem_finRange_drop_iff]

omit [Group K] in
theorem liftedSiftLevels_cons (Q : RawSchreierDatum n)
    (tables : Vector (LiftedOrbitState n K) Q.baseCount) (i : Fin Q.baseCount) :
    Q.liftedSiftLevels tables i.val =
      (Q.base.get i, tables.get i) :: Q.liftedSiftLevels tables (i.val + 1) := by
  have hi : i.val < (List.finRange Q.baseCount).length := by simp
  have hentry : (List.finRange Q.baseCount)[i.val] = i := by
    apply Fin.ext
    simp only [List.getElem_finRange, Fin.val_cast]
  simp only [liftedSiftLevels, List.drop_eq_getElem_cons hi, hentry, List.map_cons]

omit [Group K] in
theorem liftedSiftLevels_terminal (Q : RawSchreierDatum n)
    (tables : Vector (LiftedOrbitState n K) Q.baseCount) :
    Q.liftedSiftLevels tables Q.baseCount = [] := by
  have hdrop : (List.finRange Q.baseCount).drop Q.baseCount = [] :=
    List.drop_eq_nil_iff.2 (by simp)
  simp only [liftedSiftLevels, hdrop, List.map_nil]

theorem liftSift_terminal (Q : RawSchreierDatum n) (φ : K →* Equiv.Perm (Fin n))
    (U : Vector K Q.originalCount) (v : K) : LiftSift Q φ U v Q.baseCount ↔ v = 1 := by
  rw [LiftSift, liftedSiftLevels_terminal, liftSiftResidual_nil, Option.some.injEq]

theorem liftSift_mem (Q : RawSchreierDatum n) (φ : K →* Equiv.Perm (Fin n))
    (U : Vector K Q.originalCount) (i : ℕ) (v : K) (hv : LiftSift Q φ U v i) :
    v ∈ Q.liftedLevelSubgroup U i := by
  apply liftSiftResidual_mem φ _ _ ?_ v hv
  intro p hp x t ht
  obtain ⟨j, hij, rfl⟩ := (Q.mem_liftedSiftLevels_iff _ i p).1 hp
  rw [liftedOrbitTables_get] at ht
  exact Q.liftedLevelSubgroup_antitone U i j.val hij (Q.lifted_record_mem U j x t ht)

end RawSchreierDatum

end CFSG.Certificates
