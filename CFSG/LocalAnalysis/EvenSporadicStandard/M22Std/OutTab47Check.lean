module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsCheck
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.EvenSporadicStandard.M22Std.OutCheck

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck

@[expose] def nGensWords : List (List Nat) :=
  [[0, 2, 0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2]]

@[expose] def nGensTab : List Tab := nGensWords.map (wordTab letterTabs)

def bfsLayer (gens : Array Tab) (seen : Std.HashSet Tab) (frontier : Array (Tab × List Nat)) :
    Std.HashSet Tab × Array (Tab × List Nat) :=
  frontier.foldl (init := (seen, #[])) fun (seen, next) (t, w) =>
    (List.range gens.size).foldl (init := (seen, next)) fun (seen, next) i =>
      let t' := tmul gens[i]! t
      if seen.contains t' then (seen, next) else (seen.insert t', next.push (t', i :: w))

def bfsAux (gens : Array Tab) :
    Nat → Std.HashSet Tab → Array (Tab × List Nat) → Array (List Nat) → Array (List Nat)
  | 0, _, _, acc => acc
  | fuel + 1, seen, frontier, acc =>
    if frontier.isEmpty then acc else
      let (seen', next) := bfsLayer gens seen frontier
      bfsAux gens fuel seen' next (acc ++ next.map (·.2))

def bfsWords (gens : List Tab) : List (List Nat) :=
  [] :: (bfsAux gens.toArray 200 ((∅ : Std.HashSet Tab).insert idTab) #[(idTab, [])] #[]).toList

def innerWords : List (List Nat) := bfsWords nGensTab

@[expose] def tabLI : List Tab := innerWords.map (wordTab nGensTab)

@[expose] def tabL : List Tab := tabLI ++ tabLI.map (tmul betaTab)

@[expose] def keyOf (t : Tab) : Nat := t.foldl (fun a x => a * 22 + x) 0

@[expose] def strictInc : List Nat → Bool
  | a :: b :: l => decide (a < b) && strictInc (b :: l)
  | _ => true

@[expose] def nodupCheck (l : List Tab) : Bool :=
  strictInc ((l.map keyOf).mergeSort fun a b => decide (a ≤ b))

@[expose] def commGo (s t : Tab) : Tab → Tab → Bool
  | a :: as, b :: bs => (s.getD a 0 == t.getD b 0) && commGo s t as bs
  | [], [] => true
  | _, _ => false

@[expose] def commF (s t : Tab) : Bool := commGo s t t s

@[expose] def centN (L : List Tab) (t : Tab) : Nat := L.countP fun l => commF l t

@[expose] def fixF (t : Tab) : Nat := f1Tabs.countP fun x => commF t x

@[expose] def invData (L LI : List Tab) (t : Tab) : Nat × Nat × Bool × Bool :=
  (centN L t, fixF t, decide (t ∈ LI), decide (t ∈ f1Tabs))

@[expose] def invClassData : List (Nat × Nat × Bool × Bool) :=
  [(768, 16, true, true), (384, 8, false, false), (128, 8, false, false), (192, 4, false, false),
    (64, 4, true, false)]

@[expose] def classTable : List (Nat × Nat × Nat) :=
  [(768, 16, 15), (384, 8, 30), (128, 8, 90), (192, 4, 60), (64, 4, 180)]

@[expose] def classCount (D : List (Nat × Nat × Bool × Bool)) (c f : Nat) : Nat :=
  D.countP fun d => d.1 == c && d.2.1 == f

@[expose] def censusOK (L LI : List Tab) : Bool :=
  let I := L.filter isInv
  let D := I.map (invData L LI)
  decide (I.length = 375) && decide ((I.filter fun t => decide (t ∈ LI)).length = 195) &&
    D.all (fun d => decide (d ∈ invClassData)) &&
    classTable.all fun e => classCount D e.1 e.2.1 == e.2.2

@[expose] def censusCheck : Bool :=
  (nGensTab.all fun g => normOK (elemTabs 1) g) &&
    decide (tabLI.length = 5760) && nodupCheck tabLI &&
    decide (tabL.length = 11520) && nodupCheck tabL && censusOK tabL tabLI

theorem commGo_iff (s t : Tab) : ∀ a b : Tab,
    commGo s t a b = true ↔ a.map (fun j => s.getD j 0) = b.map (fun j => t.getD j 0)
  | [], [] => by simp [commGo]
  | [], _ :: _ => by simp [commGo]
  | _ :: _, [] => by simp [commGo]
  | a :: as, b :: bs => by simp [commGo, commGo_iff s t as bs]

theorem commF_iff (s t : Tab) : commF s t = true ↔ tmul s t = tmul t s := by
  rw [commF, commGo_iff]
  rfl

theorem strictInc_pairwise : ∀ l : List Nat, strictInc l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => by simp
  | a :: b :: l, h => by
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := strictInc_pairwise (b :: l) h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact h.1.trans ((List.pairwise_cons.1 ih).1 x hx)

theorem nodup_of_nodupCheck {l : List Tab} (h : nodupCheck l = true) : l.Nodup := by
  have h1 := strictInc_pairwise _ h
  have h2 : ((l.map keyOf).mergeSort fun a b => decide (a ≤ b)).Nodup := h1.imp ne_of_lt
  have h3 := (List.mergeSort_perm (l.map keyOf) fun a b => decide (a ≤ b)).nodup_iff.1 h2
  exact List.Nodup.of_map keyOf h3

theorem censusOK_spec {L LI : List Tab} (h : censusOK L LI = true) :
    (L.filter isInv).length = 375 ∧
      ((L.filter isInv).filter fun t => decide (t ∈ LI)).length = 195 ∧
      (∀ t ∈ L.filter isInv, invData L LI t ∈ invClassData) ∧
      ∀ e ∈ classTable,
        (L.filter isInv).countP (fun t => centN L t == e.1 && fixF t == e.2.1) = e.2.2 := by
  simp only [censusOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map,
    beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h195⟩, h2⟩, h3⟩ := h
  refine ⟨h1, h195, fun t ht => h2 _ ⟨t, ht, rfl⟩, fun e he => ?_⟩
  have := h3 e he
  simpa [classCount, List.countP_map, Function.comp_def, invData] using this

theorem censusCheck_spec (h : censusCheck = true) :
    (∀ g ∈ nGensTab, normOK (elemTabs 1) g = true) ∧ (tabLI.length = 5760 ∧ tabLI.Nodup) ∧
      (tabL.length = 11520 ∧ tabL.Nodup) ∧
      ((tabL.filter isInv).length = 375 ∧
        ((tabL.filter isInv).filter fun t => decide (t ∈ tabLI)).length = 195 ∧
        (∀ t ∈ tabL.filter isInv, invData tabL tabLI t ∈ invClassData) ∧
        ∀ e ∈ classTable,
          (tabL.filter isInv).countP (fun t => centN tabL t == e.1 && fixF t == e.2.1) =
            e.2.2) := by
  simp only [censusCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, ⟨h2, nodup_of_nodupCheck h3⟩, ⟨h4, nodup_of_nodupCheck h5⟩, censusOK_spec h6⟩

end CFSG.EvenSporadicStandard.M22Std.OutCheck
