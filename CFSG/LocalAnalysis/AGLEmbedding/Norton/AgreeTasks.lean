module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.SLPProd

public section

namespace CFSG.AGLEmbedding.Norton

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.AGLEmbedding.Norton.MON5_7

theorem task_get_spawn' {α : Type} (f : Unit → α) (prio : Task.Priority) :
    (Task.spawn f prio).get = f () := rfl

theorem all_and' {α : Type} (l : List α) (p q : α → Bool) :
    (l.all fun a => p a && q a) = (l.all p && l.all q) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, ih]
    cases p a <;> cases q a <;> simp

@[expose] def eqvOn (c : Native.Ctx) (v : Native.DVec) (p : List Native.Gen × List Native.Gen) :
    Bool :=
  (Native.evalWordC c p.1 v).eqv (Native.evalWordC c p.2 v)

@[expose] def agreeTasks (c : Native.Ctx) (va vb vw : Native.DVec)
    (ps : List (List Native.Gen × List Native.Gen)) : Bool :=
  ps.all (fun p => p.1.all (fun g => g.validB) && p.2.all (fun g => g.validB)) &&
    (ps.flatMap fun p => [va, vb, vw].map fun v => Task.spawn fun _ => eqvOn c v p).all Task.get

theorem agreeTasks_eq (c : Native.Ctx) (va vb vw : Native.DVec)
    (ps : List (List Native.Gen × List Native.Gen)) :
    agreeTasks c va vb vw ps = ps.all fun p => agreeC c va vb vw p.1 p.2 := by
  apply Bool.eq_iff_iff.2
  simp only [agreeTasks, agreeC, eqvOn, Bool.and_eq_true, List.all_eq_true,
    List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hv, he⟩ p hp
    exact ⟨⟨⟨⟨(hv p hp).1, (hv p hp).2⟩, he _ ⟨p, hp, va, Or.inl rfl, rfl⟩⟩,
      he _ ⟨p, hp, vb, Or.inr (Or.inl rfl), rfl⟩⟩, he _ ⟨p, hp, vw, Or.inr (Or.inr rfl), rfl⟩⟩
  · intro h
    refine ⟨fun p hp => ⟨(h p hp).1.1.1.1, (h p hp).1.1.1.2⟩, ?_⟩
    rintro _ ⟨p, hp, v, hv, rfl⟩
    rcases hv with rfl | rfl | rfl
    · exact (h p hp).1.1.2
    · exact (h p hp).1.2
    · exact (h p hp).2

theorem agreeAll_eq_agreeTasks (ps : List (List Native.Gen × List Native.Gen)) :
    agreeAll ps = agreeTasks (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) ps := by
  rw [agreeTasks_eq]
  rfl

@[expose] def prodPair (gens : Array (List Native.Gen))
    (steps : Array (ProdStep × List Native.Gen)) (k : ℕ) :
    Option (List Native.Gen × List Native.Gen) :=
  match steps[k]!.1 with
  | .gen _ => none
  | .prod l => some (steps[k]!.2, prodConcat gens steps l)
  | .inv l => some (steps[k]!.2 ++ prodConcat gens steps l, [])

@[expose] def prodIdxOK (gens : Array (List Native.Gen))
    (steps : Array (ProdStep × List Native.Gen)) (k : ℕ) : Bool :=
  match steps[k]!.1 with
  | .gen i => decide (i < gens.size)
  | .prod l => l.all fun i => decide (i < k)
  | .inv l => l.all fun i => decide (i < k)

@[expose] def prodCheckTasks (gens : Array (List Native.Gen))
    (steps : Array (ProdStep × List Native.Gen)) (lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all (prodIdxOK gens steps) &&
    agreeTasks (Native.mkCtx ()) (aV ()) (bV ()) (wV ())
      ((List.range' lo (hi - lo)).filterMap (prodPair gens steps))

theorem prodStepOKC_eq_split (c : Native.Ctx) (va vb vw : Native.DVec)
    (gens : Array (List Native.Gen)) (steps : Array (ProdStep × List Native.Gen)) (k : ℕ) :
    prodStepOKC c va vb vw gens steps k =
      (prodIdxOK gens steps k && (prodPair gens steps k).all fun p => agreeC c va vb vw p.1 p.2) := by
  unfold prodStepOKC prodIdxOK prodPair
  rcases steps[k]!.1 with i | l | l <;> simp

theorem prodCheck_eq_prodCheckTasks (gens : Array (List Native.Gen))
    (steps : Array (ProdStep × List Native.Gen)) (lo hi : ℕ) :
    prodCheck gens steps lo hi = prodCheckTasks gens steps lo hi := by
  have e : prodStepOKC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) gens steps = fun k =>
      (prodIdxOK gens steps k && (prodPair gens steps k).all fun p =>
        agreeC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) p.1 p.2) :=
    funext (prodStepOKC_eq_split _ _ _ _ gens steps)
  unfold prodCheck prodCheckTasks
  dsimp only
  rw [e, all_and', agreeTasks_eq, List.all_filterMap]
  rfl

@[expose] def moveTasks (ws : List (List Native.Gen)) (v : Native.DVec) : Bool :=
  let c := Native.mkCtx ()
  ws.all (fun w => w.all fun g => g.validB) &&
    (ws.map fun w => Task.spawn fun _ => EdgeNoncomm.moveCheckAux (Native.evalWordC c w v) v).all
      Task.get

theorem all_moveCheck_eq_moveTasks {α : Type} (l : List α) (f : α → List Native.Gen)
    (v : Native.DVec) :
    (l.all fun a => EdgeNoncomm.moveCheck (f a) v) = moveTasks (l.map f) v := by
  simp only [moveTasks, EdgeNoncomm.moveCheck, Native.evalWord, List.all_map, Function.comp_def,
    task_get_spawn']
  exact all_and' l _ _

end CFSG.AGLEmbedding.Norton
