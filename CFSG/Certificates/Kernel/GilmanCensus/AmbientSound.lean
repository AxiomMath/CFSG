module

import all Certificates.Data.Census
public import CFSG.Certificates.Kernel.GilmanCensus.MemoSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

@[expose] def LoopResG {α β σ : Type} (P : α → Bool) (w : α → β) (Q : α → σ → σ → Prop)
    (l : List α) (s : σ) (r : (Option β × Unit) × σ) : Prop :=
  match l.find? P with
  | none => r = ((none, ()), s)
  | some a => r.1 = (some (w a), ()) ∧ Q a s r.2

theorem sloopG {α β σ : Type} (I : σ → Prop) (P : α → Bool) (w : α → β) (Q : α → σ → σ → Prop)
    (f : α → Option β × Unit → StateT σ Id (ForInStep (Option β × Unit)))
    (hf : ∀ a st s, I s → if P a then ((f a st).run s).1 = ForInStep.done (some (w a), ()) ∧
        Q a s ((f a st).run s).2 else (f a st).run s = (ForInStep.yield (none, ()), s)) :
    ∀ (l : List α) (s : σ), I s → LoopResG P w Q l s ((forIn l (none, ()) f).run s)
  | [], s, _ => rfl
  | a :: l, s, hs => by
    unfold LoopResG
    rw [List.forIn_cons, StateT.run_bind, List.find?_cons]
    have h := hf a (none, ()) s hs
    by_cases hp : P a = true
    · simp only [hp, ↓reduceIte] at h ⊢
      rw [idBind]
      generalize (f a (none, ())).run s = r at h ⊢
      obtain ⟨v, s'⟩ := r
      obtain ⟨h1, h2⟩ := h
      simp only at h1 h2
      subst h1
      exact ⟨rfl, h2⟩
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [h, idBind]
      exact sloopG I P w Q f hf l s hs

abbrev AW := (Nat × Nat) × Int × Int

@[expose] def aV (dt : Data) (J : Nat) (b : Nat × Int) (i : Nat) (sg : Int) : Array (Nat × Int) :=
  ((Array.map (fun i => (i, (1 : Int))) (simpOf dt J)).push b).push (i, sg)

@[expose] def aAct (dt : Data) (L : Nat) (V : Array (Nat × Int)) (w : AW) :
    CM (ForInStep (Option (Option AW) × Unit)) := do
  if rank3 (V.map fun v => dt.H[v.1]!) dt.d != dt.d then markBad
  if closureOf dt ((V.extract 0 (V.size - 1)).map (fun x : Nat × Int => x.1)) != L then markBad
  return ForInStep.done (some (some w), ())

@[expose] def aInner (dt : Data) (J L K : Nat) (b : Nat × Int) (i : Nat) (sg : Int)
    (_ : Option (Option AW) × Unit) : CM (ForInStep (Option (Option AW) × Unit)) :=
  match diagram dt (aV dt J b i sg) with
  | none => pure (ForInStep.yield (none, ()))
  | some (C, dd) =>
    if (dd % 3 == 0 || (aV dt J b i sg).size != dt.d) = true then pure (ForInStep.yield (none, ()))
    else if (detInt ((C.extract 0 (C.size - 1)).map fun r => r.extract 0 (r.size - 1)) % 3 == 0) = true
    then pure (ForInStep.yield (none, ()))
    else if (closureOf dt ((aV dt J b i sg).map (fun x : Nat × Int => x.1)) !=
        closureOf dt (bitsOf (L ||| K))) = true then pure (ForInStep.yield (none, ()))
    else aAct dt L (aV dt J b i sg) (kindOf dt (closureOf dt (bitsOf (L ||| K))), dd,
      detInt ((C.extract 0 (C.size - 1)).map fun r => r.extract 0 (r.size - 1)))

@[expose] def aMid (dt : Data) (J L K : Nat) (b : Nat × Int) (i : Nat)
    (_ : Option (Option AW) × Unit) : CM (ForInStep (Option (Option AW) × Unit)) := do
  let r ← forIn [(1 : Int), -1] ((none : Option (Option AW)), ()) (aInner dt J L K b i)
  match r.1 with
  | some x => pure (ForInStep.done (some x, ()))
  | none => pure (ForInStep.yield (none, ()))

@[expose] def aOuter (dt : Data) (J L K : Nat) (b : Nat × Int)
    (_ : Option (Option AW) × Unit) : CM (ForInStep (Option (Option AW) × Unit)) := do
  let r ← forIn (bitsOf (closureOf dt (bitsOf (L ||| K)) ^^^ (closureOf dt (bitsOf (L ||| K)) &&& L)))
    ((none : Option (Option AW)), ()) (aMid dt J L K b)
  match r.1 with
  | some x => pure (ForInStep.done (some x, ()))
  | none => pure (ForInStep.yield (none, ()))

@[expose] def aProg (dt : Data) (J L K : Nat) : CM (Option AW) := do
  let r ← forIn (extensions dt J L) ((none : Option (Option AW)), ()) (aOuter dt J L K)
  match r.1 with
  | some x => pure x
  | none => pure none

theorem ambientM_prog (dt : Data) (J L K : Nat) : ambientM dt J L K = aProg dt J L K := by
  unfold ambientM aProg aOuter aMid aInner aAct aV
  dsimp only
  congr 1
  all_goals first
    | (funext p; obtain ⟨o, u⟩ := p; cases o <;> rfl)
    | skip
  congr 1
  funext b st
  congr 1
  all_goals first
    | (funext p; obtain ⟨o, u⟩ := p; cases o <;> rfl)
    | skip
  congr 1
  funext i st2
  congr 1
  all_goals first
    | (funext p; obtain ⟨o, u⟩ := p; cases o <;> rfl)
    | skip

@[expose] def aTry (dt : Data) (J L K : Nat) (b : Nat × Int) (i : Nat) (sg : Int) : Option AW :=
  match diagram dt (aV dt J b i sg) with
  | none => none
  | some (C, dd) =>
    if (dd % 3 == 0 || (aV dt J b i sg).size != dt.d) = true then none
    else if (detInt ((C.extract 0 (C.size - 1)).map fun r => r.extract 0 (r.size - 1)) % 3 == 0) = true
    then none
    else if (closureOf dt ((aV dt J b i sg).map (fun x : Nat × Int => x.1)) !=
        closureOf dt (bitsOf (L ||| K))) = true then none
    else some (kindOf dt (closureOf dt (bitsOf (L ||| K))), dd,
      detInt ((C.extract 0 (C.size - 1)).map fun r => r.extract 0 (r.size - 1)))

@[expose] def aBad (dt : Data) (L : Nat) (V : Array (Nat × Int)) : Bool :=
  rank3 (V.map fun v => dt.H[v.1]!) dt.d != dt.d ||
    closureOf dt ((V.extract 0 (V.size - 1)).map (fun x : Nat × Int => x.1)) != L

@[expose] def AStep (dt : Data) (L : Nat) (V : Array (Nat × Int)) (s s' : Cache) : Prop :=
  (CacheOK dt s → CacheOK dt s') ∧ s'.bad = (s.bad || aBad dt L V)

theorem aact (dt : Data) (L : Nat) (V : Array (Nat × Int)) (w : AW) (s : Cache) :
    ((aAct dt L V w).run s).1 = ForInStep.done (some (some w), ()) ∧
      AStep dt L V s ((aAct dt L V w).run s).2 := by
  unfold aAct
  simp only [StateT.run_bind]
  split
  · rename_i h1
    rw [StateT.run_bind]
    split
    · rename_i h2
      refine ⟨rfl, fun hs => ⟨hs.1, hs.2⟩, ?_⟩
      simp only [aBad, h1, Bool.true_or, Bool.or_true]
      rfl
    · rename_i h2
      refine ⟨rfl, fun hs => ⟨hs.1, hs.2⟩, ?_⟩
      simp only [aBad, h1, Bool.true_or, Bool.or_true]
      rfl
  · rename_i h1
    split
    · rename_i h2
      refine ⟨rfl, fun hs => ⟨hs.1, hs.2⟩, ?_⟩
      simp only [aBad, h2, Bool.or_true]
      rfl
    · rename_i h2
      refine ⟨rfl, fun hs => hs, ?_⟩
      simp only [Bool.not_eq_true] at h1 h2
      simp only [aBad, h1, h2, Bool.or_false]
      rfl

theorem ainner (dt : Data) (J L K : Nat) (b : Nat × Int) (i : Nat) (sg : Int)
    (st : Option (Option AW) × Unit) (s : Cache) :
    if (aTry dt J L K b i sg).isSome then
      ((aInner dt J L K b i sg st).run s).1 = ForInStep.done (some (aTry dt J L K b i sg), ()) ∧
        AStep dt L (aV dt J b i sg) s ((aInner dt J L K b i sg st).run s).2
    else (aInner dt J L K b i sg st).run s = (ForInStep.yield (none, ()), s) := by
  unfold aInner aTry
  split
  · rfl
  · rename_i C dd _
    split
    · rfl
    split
    · rfl
    split
    · rfl
    exact aact dt L _ _ s

theorem find_findSome {α β : Type} (g : α → Option β) : ∀ (l : List α) (x : α),
    l.find? (fun x => (g x).isSome) = some x → l.findSome? g = g x
  | [], _, h => by simp at h
  | y :: l, x, h => by
    rw [List.find?_cons] at h
    rw [List.findSome?_cons]
    split at h
    · rename_i hy
      cases h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hy
      rw [hv]
    · rename_i hy
      have : g y = none := by simpa using hy
      rw [this]
      exact find_findSome g l x h

theorem find_findSome_none {α β : Type} (g : α → Option β) : ∀ (l : List α),
    l.find? (fun x => (g x).isSome) = none → l.findSome? g = none
  | [], _ => rfl
  | y :: l, h => by
    rw [List.find?_cons] at h
    rw [List.findSome?_cons]
    split at h
    · simp at h
    · rename_i hy
      have : g y = none := by simpa using hy
      rw [this]
      exact find_findSome_none g l h

@[expose] def aMidW (dt : Data) (J L K : Nat) (b : Nat × Int) (i : Nat) : Option AW :=
  [(1 : Int), -1].findSome? (aTry dt J L K b i)

@[expose] def aOutW (dt : Data) (J L K : Nat) (b : Nat × Int) : Option AW :=
  (bitsOf (closureOf dt (bitsOf (L ||| K)) ^^^ (closureOf dt (bitsOf (L ||| K)) &&& L))).toList.findSome?
    (aMidW dt J L K b)

theorem amid (dt : Data) (J L K : Nat) (b : Nat × Int) (i : Nat) (st : Option (Option AW) × Unit)
    (s : Cache) :
    if (aMidW dt J L K b i).isSome then
      ((aMid dt J L K b i st).run s).1 = ForInStep.done (some (aMidW dt J L K b i), ()) ∧
        ∃ sg, [(1 : Int), -1].find? (fun sg => (aTry dt J L K b i sg).isSome) = some sg ∧
          AStep dt L (aV dt J b i sg) s ((aMid dt J L K b i st).run s).2 ∧
          aTry dt J L K b i sg = aMidW dt J L K b i
    else (aMid dt J L K b i st).run s = (ForInStep.yield (none, ()), s) := by
  have h := sloopG (fun _ => True) (fun sg => (aTry dt J L K b i sg).isSome) (aTry dt J L K b i)
    (fun sg => AStep dt L (aV dt J b i sg)) (aInner dt J L K b i)
    (fun sg st s _ => ainner dt J L K b i sg st s) [(1 : Int), -1] s trivial
  unfold aMid
  rw [StateT.run_bind]
  unfold LoopResG at h
  generalize (forIn [(1 : Int), -1] (none, ()) (aInner dt J L K b i)).run s = r at h ⊢
  split at h
  · rename_i hf
    have e := find_findSome_none (aTry dt J L K b i) _ hf
    unfold aMidW
    rw [e, h]
    rfl
  · rename_i sg hf
    have e := find_findSome (aTry dt J L K b i) _ sg hf
    have hs : (aTry dt J L K b i sg).isSome := by
      have := List.find?_some hf
      simpa using this
    unfold aMidW
    rw [e]
    obtain ⟨⟨o, u⟩, s'⟩ := r
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    cases h1
    rw [if_pos hs]
    exact ⟨rfl, sg, hf, h2, rfl⟩

theorem aouter (dt : Data) (J L K : Nat) (b : Nat × Int) (st : Option (Option AW) × Unit)
    (s : Cache) :
    if (aOutW dt J L K b).isSome then
      ((aOuter dt J L K b st).run s).1 = ForInStep.done (some (aOutW dt J L K b), ()) ∧
        ∃ i sg, (bitsOf (closureOf dt (bitsOf (L ||| K)) ^^^
            (closureOf dt (bitsOf (L ||| K)) &&& L))).toList.find? (fun i => (aMidW dt J L K b i).isSome) =
            some i ∧ [(1 : Int), -1].find? (fun sg => (aTry dt J L K b i sg).isSome) = some sg ∧
          AStep dt L (aV dt J b i sg) s ((aOuter dt J L K b st).run s).2 ∧
          aTry dt J L K b i sg = aOutW dt J L K b
    else (aOuter dt J L K b st).run s = (ForInStep.yield (none, ()), s) := by
  have h := sloopG (fun _ => True) (fun i => (aMidW dt J L K b i).isSome) (aMidW dt J L K b)
    (fun i s s' => ∃ sg, [(1 : Int), -1].find? (fun sg => (aTry dt J L K b i sg).isSome) = some sg ∧
      AStep dt L (aV dt J b i sg) s s' ∧ aTry dt J L K b i sg = aMidW dt J L K b i)
    (aMid dt J L K b) (fun i st s _ => amid dt J L K b i st s)
    (bitsOf (closureOf dt (bitsOf (L ||| K)) ^^^ (closureOf dt (bitsOf (L ||| K)) &&& L))).toList s
    trivial
  unfold aOuter
  rw [StateT.run_bind, ← Array.forIn_toList]
  unfold LoopResG at h
  generalize (forIn (bitsOf (closureOf dt (bitsOf (L ||| K)) ^^^
    (closureOf dt (bitsOf (L ||| K)) &&& L))).toList (none, ()) (aMid dt J L K b)).run s = r at h ⊢
  split at h
  · rename_i hf
    have e := find_findSome_none (aMidW dt J L K b) _ hf
    unfold aOutW
    rw [e, h]
    rfl
  · rename_i i hf
    have e := find_findSome (aMidW dt J L K b) _ i hf
    have hs : (aMidW dt J L K b i).isSome := by
      have := List.find?_some hf
      simpa using this
    unfold aOutW
    rw [e]
    obtain ⟨⟨o, u⟩, s'⟩ := r
    obtain ⟨h1, sg, h0, h2, h3⟩ := h
    simp only at h1 h2 h3
    cases h1
    rw [if_pos hs]
    exact ⟨rfl, i, sg, hf, h0, h2, h3⟩

@[expose] def aWit (dt : Data) (J L K : Nat) : Option AW :=
  (extensions dt J L).toList.findSome? (aOutW dt J L K)

theorem ambientM_ok (dt : Data) (J L K : Nat) (c : Cache) :
    ((ambientM dt J L K).run c).1 = aWit dt J L K ∧
      (aWit dt J L K = none → ((ambientM dt J L K).run c).2 = c) ∧
      (∀ x, aWit dt J L K = some x → ∃ b i sg,
        (extensions dt J L).toList.find? (fun b => (aOutW dt J L K b).isSome) = some b ∧
        (bitsOf (closureOf dt (bitsOf (L ||| K)) ^^^
          (closureOf dt (bitsOf (L ||| K)) &&& L))).toList.find? (fun i => (aMidW dt J L K b i).isSome) =
          some i ∧ [(1 : Int), -1].find? (fun sg => (aTry dt J L K b i sg).isSome) = some sg ∧
        aTry dt J L K b i sg = some x ∧
        AStep dt L (aV dt J b i sg) c ((ambientM dt J L K).run c).2) := by
  have h := sloopG (fun _ => True) (fun b => (aOutW dt J L K b).isSome) (aOutW dt J L K)
    (fun b s s' => ∃ i sg, (bitsOf (closureOf dt (bitsOf (L ||| K)) ^^^
        (closureOf dt (bitsOf (L ||| K)) &&& L))).toList.find? (fun i => (aMidW dt J L K b i).isSome) =
        some i ∧ [(1 : Int), -1].find? (fun sg => (aTry dt J L K b i sg).isSome) = some sg ∧
      AStep dt L (aV dt J b i sg) s s' ∧ aTry dt J L K b i sg = aOutW dt J L K b)
    (aOuter dt J L K) (fun b st s _ => aouter dt J L K b st s) (extensions dt J L).toList c trivial
  rw [ambientM_prog]
  unfold aProg
  rw [StateT.run_bind, ← Array.forIn_toList]
  unfold LoopResG at h
  generalize (forIn (extensions dt J L).toList (none, ()) (aOuter dt J L K)).run c = r at h ⊢
  split at h
  · rename_i hf
    have e := find_findSome_none (aOutW dt J L K) _ hf
    unfold aWit
    rw [e, h]
    exact ⟨rfl, fun _ => rfl, fun x hx => by simp at hx⟩
  · rename_i b hf
    have e := find_findSome (aOutW dt J L K) _ b hf
    unfold aWit
    rw [e]
    obtain ⟨⟨o, u⟩, s'⟩ := r
    obtain ⟨h1, i, sg, hi, hs0, h2, h3⟩ := h
    simp only at h1 h2 h3
    cases h1
    refine ⟨rfl, fun hn => ?_, fun x hx => ⟨b, i, sg, hf, hi, hs0, h3.trans hx, h2⟩⟩
    have hs : (aOutW dt J L K b).isSome := by
      have := List.find?_some hf
      simpa using this
    rw [hn] at hs
    simp at hs

end Certificates.GilmanCensusK

end
