module

public import CFSG.Certificates.Kernel.GilmanCensus.RankSound
public import Certificates.Data.Kernel.GilmanCensus.RootsK
import all Certificates.Data.Census

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

@[expose] def simpleA (n : Nat) : Array IVec :=
  Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j => if i.val == j.val then 1 else 0

@[expose] def grF (A : Array (Array Int)) (r : Array Int) (s : HashSet IVec × Array IVec × Array IVec)
    (i : Nat) : HashSet IVec × Array IVec × Array IVec :=
  let c := Id.run (forIn [0:A.size] (0 : Int) fun j c => pure (ForInStep.yield (c + r[j]! * A[j]![i]!)))
  let s' := r.set! i (r[i]! - c)
  if ((s'.all fun x => decide (x ≥ 0)) && !s.1.contains s') = true then
    (s.1.insert s', s.2.1.push s', s.2.2.push s')
  else s

@[expose] def grInner (A : Array (Array Int)) (r : Array Int) (i : Nat)
    (s : HashSet IVec × Array IVec × Array IVec) :
    Id (ForInStep (HashSet IVec × Array IVec × Array IVec)) :=
  let c := Id.run (forIn [0:A.size] (0 : Int) fun j c => pure (ForInStep.yield (c + r[j]! * A[j]![i]!)))
  let s' := r.set! i (r[i]! - c)
  if ((s'.all fun x => decide (x ≥ 0)) && !s.1.contains s') = true then
    pure (ForInStep.yield (s.1.insert s', s.2.1.push s', s.2.2.push s'))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2))

@[expose] def grOuter (A : Array (Array Int)) (_ : Unit) (s : HashSet IVec × Array IVec × Array IVec) :
    Id (ForInStep (HashSet IVec × Array IVec × Array IVec)) :=
  if s.2.1.size > 0 then
    pure (ForInStep.yield (Id.run (forIn [0:A.size] (s.1, s.2.1.pop, s.2.2) (grInner A s.2.1.back!))))
  else pure (ForInStep.done (s.1, s.2.1, s.2.2))

@[expose] def grSeed (n : Nat) : HashSet IVec :=
  Id.run (forIn (simpleA n) (∅ : HashSet IVec) fun s seen => pure (ForInStep.yield (seen.insert s)))

theorem genRoots_run (A : Array (Array Int)) : genRoots A =
    (Id.run (forIn (m := Id) Lean.Loop.mk (grSeed A.size, simpleA A.size, simpleA A.size)
      (grOuter A))).2.2 := by
  unfold genRoots
  rfl

@[expose] def GR (s : HashSet IVec × Array IVec × Array IVec) (t : List (List Int) × List (List Int)) :
    Prop :=
  LLI s.2.1 = t.1 ∧ LLI s.2.2 = t.2 ∧ ∀ v : IVec, s.1.contains v = t.2.contains v.toList

theorem colSum_eq (A : Array (Array Int)) (r : Array Int) (i : Nat) :
    Id.run (forIn [0:A.size] (0 : Int) fun j c => pure (ForInStep.yield (c + r[j]! * A[j]![i]!))) =
      colSumK (LLI A) A.size r.toList i := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [List.forIn_pure_yield_eq_foldl]
  simp only [Id.run_pure, getElem!_eq_getD_toListI, getRowI]
  rfl

theorem set!_toList (r : Array Int) (i : Nat) (x : Int) : (r.set! i x).toList = r.toList.set i x := by
  simp [Array.set!]

theorem arr_beq (s v : Array Int) : (s == v) = (v.toList == s.toList) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Array.toList_inj]
  exact eq_comm

theorem LLI_push (a : Array (Array Int)) (x : Array Int) : LLI (a.push x) = LLI a ++ [x.toList] := by
  simp [LLI]

theorem contains_snoc (l : List (List Int)) (x y : List Int) :
    (l ++ [x]).contains y = (y == x || l.contains y) := by
  rw [Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, List.mem_append, List.mem_singleton, Bool.or_eq_true, beq_iff_eq]
  exact Or.comm

theorem grInner_yield (A : Array (Array Int)) (r : Array Int) (i : Nat)
    (s : HashSet IVec × Array IVec × Array IVec) :
    grInner A r i s = ForInStep.yield (grF A r s i) := by
  unfold grInner grF
  dsimp only
  split <;> rfl

theorem gr_step (A : Array (Array Int)) (r : Array Int) (i : Nat)
    (s : HashSet IVec × Array IVec × Array IVec) (t : List (List Int) × List (List Int)) (h : GR s t) :
    GR (grF A r s i) (grStep (LLI A) A.size r.toList t i) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold grF grStep
  dsimp only
  rw [colSum_eq]
  have e : r.toList.set i (r.toList.getD i 0 - colSumK (LLI A) A.size r.toList i) =
      (r.set! i (r[i]! - colSumK (LLI A) A.size r.toList i)).toList := by
    rw [set!_toList, getElem!_eq_getD_toListI]
  rw [e]
  generalize r.set! i (r[i]! - colSumK (LLI A) A.size r.toList i) = s'
  rw [← Array.all_toList, h3 s']
  cases hc : (s'.toList.all (fun x => decide (x ≥ 0)) && !t.2.contains s'.toList)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨h1, h2, h3⟩
  · simp only [↓reduceIte]
    refine ⟨by rw [LLI_push, h1], by rw [LLI_push, h2], fun v => ?_⟩
    rw [HashSet.contains_insert, h3 v, arr_beq, contains_snoc]

theorem gr_fold (A : Array (Array Int)) (r : Array Int) : ∀ (l : List Nat)
    (s : HashSet IVec × Array IVec × Array IVec) (t : List (List Int) × List (List Int)), GR s t →
    GR (l.foldl (grF A r) s) (l.foldl (grStep (LLI A) A.size r.toList) t)
  | [], _, _, h => h
  | i :: l, s, t, h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact gr_fold A r l _ _ (gr_step A r i s t h)

theorem gr_inner (A : Array (Array Int)) (r : Array Int) (s : HashSet IVec × Array IVec × Array IVec)
    (t : List (List Int) × List (List Int)) (h : GR s t) :
    GR (Id.run (forIn [0:A.size] s (grInner A r)))
      ((List.range' 0 A.size).foldl (grStep (LLI A) A.size r.toList) t) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yield (fun s i => grF A r s i) _ (fun i s => grInner_yield A r i s)]
  exact gr_fold A r _ s t h

theorem LLI_pop (a : Array (Array Int)) : LLI a.pop = (LLI a).dropLast := by
  simp [LLI, List.map_dropLast]

theorem LLI_back (a : Array (Array Int)) (h : 0 < a.size) :
    (LLI a).getLast? = some a.back!.toList := by
  have e : a = a.pop.push a.back! := Array.eq_push_pop_back!_of_size_ne_zero (by omega)
  rw [e, LLI_push, List.getLast?_append, List.getLast?_singleton]
  rw [← e]
  rfl

theorem gr_outer (A : Array (Array Int)) : ∀ (f : Nat) (s : HashSet IVec × Array IVec × Array IVec)
    (t : List (List Int) × List (List Int)) (res : List (List Int)), GR s t →
    grGo (LLI A) A.size f t.1 t.2 = some res →
    LLI (Id.run (forIn (m := Id) Lean.Loop.mk s (grOuter A))).2.2 = res
  | 0, _, _, _, _, hg => by simp [grGo] at hg
  | f + 1, s, t, res, h, hg => by
    rw [loop_unfold]
    by_cases h0 : s.2.1.size > 0
    · simp only [grOuter, h0, ↓reduceIte]
      have hb := LLI_back s.2.1 h0
      rw [h.1] at hb
      rw [grGo, hb] at hg
      dsimp only at hg
      have hs : GR (s.1, s.2.1.pop, s.2.2) (t.1.dropLast, t.2) :=
        ⟨by rw [LLI_pop, h.1], h.2.1, h.2.2⟩
      exact gr_outer A f _ _ res (gr_inner A s.2.1.back! _ _ hs) hg
    · simp only [grOuter, h0, ↓reduceIte]
      have e : t.1 = [] := by
        rw [← h.1, LLI, List.map_eq_nil_iff]
        apply List.eq_nil_of_length_eq_zero
        rw [Array.length_toList]
        omega
      rw [grGo, e] at hg
      simp only [List.getLast?_nil, Option.some.injEq] at hg
      rw [← hg]
      exact h.2.1

theorem grSeed_contains (n : Nat) (v : IVec) :
    (grSeed n).contains v = (LLI (simpleA n)).contains v.toList := by
  unfold grSeed
  rw [← Array.forIn_toList, List.forIn_pure_yield_eq_foldl]
  simp only [Id.run_pure]
  have : ∀ (l : List IVec) (S : HashSet IVec) (L : List (List Int)),
      (∀ w : IVec, S.contains w = L.contains w.toList) →
      (l.foldl (fun seen s => seen.insert s) S).contains v = (L ++ l.map Array.toList).contains v.toList := by
    intro l
    induction l with
    | nil => intro S L hS; simp [hS v]
    | cons x l ih =>
      intro S L hS
      rw [List.foldl_cons, List.map_cons, ← List.singleton_append, ← List.append_assoc]
      apply ih
      intro w
      rw [HashSet.contains_insert, hS w, arr_beq, contains_snoc]
  rw [this (simpleA n).toList ∅ [] (fun w => by simp)]
  simp [LLI]

theorem genRoots_eq (A : Array (Array Int)) (f : Nat) (res : List (List Int))
    (h : grGo (LLI A) A.size f (LLI (simpleA A.size)) (LLI (simpleA A.size)) = some res) :
    LLI (genRoots A) = res := by
  rw [genRoots_run]
  exact gr_outer A f _ (LLI (simpleA A.size), LLI (simpleA A.size)) res
    ⟨rfl, rfl, grSeed_contains A.size⟩ h

theorem cartan_mode (m : Nat) (hm : m < 6) :
    LLI (cartanMat (m == 0) (rankOf m)) = cartanK (m == 0) (rankOf m) ∧
      (cartanMat (m == 0) (rankOf m)).size = rankOf m ∧ LLI (simpleA (rankOf m)) = simpleK (rankOf m) :=
  match m, hm with
  | 0, _ => by decide +kernel
  | 1, _ => by decide +kernel
  | 2, _ => by decide +kernel
  | 3, _ => by decide +kernel
  | 4, _ => by decide +kernel
  | 5, _ => by decide +kernel
  | _ + 6, h => absurd h (by omega)

theorem genRoots_mode (m : Nat) (hm : m < 6) (AR : List (List Nat)) (h : rootsOkK m AR = true) :
    LLI (genRoots (cartanMat (m == 0) (rankOf m))) = toI AR := by
  obtain ⟨e1, e2, e3⟩ := cartan_mode m hm
  unfold rootsOkK at h
  apply genRoots_eq _ 200
  rw [e1, e2, e3]
  exact eq_of_beq h

end Certificates.GilmanCensusK

end
