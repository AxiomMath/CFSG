module

public import CFSG.Sporadic.Schreier.J1CentData

public section

namespace CFSG.KS.ClassLab

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def labLoop (N : Nat) (F : Nat → Nat → Nat → Bool) : Array Nat × Array Nat × Array Nat :=
  Id.run do
  let mut reps : Array Nat := #[]
  let mut lab : Array Nat := Array.replicate N 0
  let mut cj : Array Nat := Array.replicate N 0
  let mut done : Array Bool := Array.replicate N false
  for i in [0:N] do
    if !done[i]! then
      let r := reps.size
      reps := reps.push i
      for c in [0:N] do
        for k in [0:N] do
          if !done[k]! && F k c i then
            done := done.set! k true
            lab := lab.set! k r
            cj := cj.set! k c
  return (reps, lab, cj)

theorem classLabels_eq (n : Nat) (E : Array Table) :
    CFSG.Sporadic.Schreier.classLabels n E = labLoop E.size
      (fun k c i => tblEq n E[k]! (conjT n E[c]! (E.map (invT n))[c]! E[i]!)) :=
  rfl

abbrev St3 := Array Nat × Array Nat × Array Bool

@[expose] def kBody (F : Nat → Nat → Nat → Bool) (c i r k : Nat) (s : St3) : Id (ForInStep St3) :=
  if (!s.2.2[k]! && F k c i) = true then
    pure (ForInStep.yield (s.1.set! k r, s.2.1.set! k c, s.2.2.set! k true))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2))

@[expose] def cBody (N : Nat) (F : Nat → Nat → Nat → Bool) (i r c : Nat) (s : St3) :
    Id (ForInStep St3) :=
  pure (ForInStep.yield (Id.run (forIn (List.range' 0 N) (s.1, s.2.1, s.2.2) (kBody F c i r))))

@[expose] def oBody (N : Nat) (F : Nat → Nat → Nat → Bool) (i : Nat)
    (s : Array Nat × St3) : Id (ForInStep (Array Nat × St3)) :=
  if (!s.2.2.2[i]!) = true then
    pure (ForInStep.yield (s.1.push i,
      Id.run (forIn (List.range' 0 N) (s.2.1, s.2.2.1, s.2.2.2) (cBody N F i s.1.size))))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def labR (N : Nat) (F : Nat → Nat → Nat → Bool) : Array Nat × Array Nat × Array Nat :=
  let s := Id.run (forIn (List.range' 0 N)
    ((#[] : Array Nat), Array.replicate N 0, Array.replicate N 0, Array.replicate N false)
    (oBody N F))
  (s.1, s.2.1, s.2.2.1)

theorem labLoop_eq (N : Nat) (F : Nat → Nat → Nat → Bool) : labLoop N F = labR N F := by
  unfold labLoop labR
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem forIn_congr_mem {β : Type} {l : List Nat} {b : β} {f g : Nat → β → Id (ForInStep β)}
    (h : ∀ x ∈ l, ∀ s, f x s = g x s) : forIn l b f = forIn l b g := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    rw [List.forIn_cons, List.forIn_cons, h x List.mem_cons_self b]
    congr 1
    funext s
    cases s with
    | done => rfl
    | yield s => exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem labR_congr {N : Nat} {F F' : Nat → Nat → Nat → Bool}
    (h : ∀ k < N, ∀ c < N, ∀ i < N, F k c i = F' k c i) : labR N F = labR N F' := by
  have mem : ∀ {x : Nat}, x ∈ List.range' 0 N → x < N := fun hx => by
    rw [List.mem_range'_1] at hx
    omega
  have hk : ∀ c < N, ∀ i < N, ∀ r k, k < N → ∀ s, kBody F c i r k s = kBody F' c i r k s := by
    intro c hc i hi r k hk s
    unfold kBody
    rw [h k hk c hc i hi]
  have hc : ∀ i < N, ∀ r c, c < N → ∀ s, cBody N F i r c s = cBody N F' i r c s := by
    intro i hi r c hc s
    unfold cBody
    rw [forIn_congr_mem fun k hk' s' => hk c hc i hi r k (mem hk') s']
  have ho : ∀ i, i < N → ∀ s, oBody N F i s = oBody N F' i s := by
    intro i hi s
    unfold oBody
    rw [forIn_congr_mem fun c hc' s' => hc i hi s.1.size c (mem hc') s']
  unfold labR
  rw [forIn_congr_mem fun i hi s => ho i (mem hi) s]

@[expose] def labOK (t : Array Nat × Array Nat × Array Nat) (R L C : List Nat) : Bool :=
  t.1.toList == R && t.2.1.toList == L && t.2.2.toList == C

theorem eq_of_labOK {t : Array Nat × Array Nat × Array Nat} {R L C : List Nat}
    (h : labOK t R L C = true) : t = (R.toArray, L.toArray, C.toArray) := by
  unfold labOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨a, b, c⟩ := t
  simp only at h1 h2 h3
  rw [← h1, ← h2, ← h3]

end CFSG.KS.ClassLab

end
