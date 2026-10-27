module

public import Certificates.Data.Kernel.LocalComp.ThreeW

public section

namespace CFSG.KC.LocalComp.Spec

open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native CFSG.KC.LocalComp.ThreeW

abbrev ClosSt : Type := Array Table × Array Nat × Array Nat × List Nat

abbrev NatSt : Type := Std.HashSet Nat × Array Table × Array Nat × Array Nat

@[expose] def SameSt (s : NatSt) (σ : ClosSt) : Prop :=
  s.2.1 = σ.1 ∧ s.2.2.1 = σ.2.1 ∧ s.2.2.2 = σ.2.2.1 ∧ ∀ k, s.1.contains k = σ.2.2.2.contains k

@[expose] def OutSt (s : NatSt) (t : Array Table × Array Nat × Array Nat) : Prop :=
  (s.2.1, s.2.2.1, s.2.2.2) = t

theorem allFrom_eq_nat_all (lo : Nat) (p : Nat → Bool) (m : Nat) :
    allFrom lo p m = Nat.all m (fun k _ => p (lo + k)) := by
  induction m with
  | zero => simp only [allFrom, Nat.all_zero]
  | succ m ih => simp only [allFrom, Nat.all_succ, ih]

theorem allInK_eq_allIn (lo hi : Nat) (p : Nat → Bool) : allInK lo hi p = allIn lo hi p := by
  unfold allInK allIn
  exact allFrom_eq_nat_all lo p (hi - lo)

theorem tblEqK_eq_tblEq (n : Nat) (S T : Table) : tblEqK n S T = tblEq n S T := by
  unfold tblEqK tblEq
  exact allInK_eq_allIn _ _ _

theorem commTK_eq_commT (n : Nat) (x y : Table) : commTK n x y = commT n x y := by
  unfold commTK commT
  exact tblEqK_eq_tblEq _ _ _

theorem powFixWK_eq_powFixW (n : Nat) (w : List Table) (e : Nat) :
    powFixWK n w e = powFixW n w e := by
  unfold powFixWK powFixW
  exact allInK_eq_allIn _ _ _

theorem ordTestK_eq_ordTest (n m : Nat) (T : Table) : ordTestK n m T = ordTest n m T := by
  simp only [ordTestK, ordTest, ordW, powFixWK_eq_powFixW]

theorem conjTreeOKK_eq_conjTreeOK (n : Nat) (gens gensInv : Array Table) (x : Table)
    (elts : Array Table) (par lab : Array Nat) :
    conjTreeOKK n gens gensInv x elts par lab = conjTreeOK n gens gensInv x elts par lab := by
  simp only [conjTreeOKK, conjTreeOK, tblEqK_eq_tblEq, allInK_eq_allIn]

theorem spec_getElem!_push {α : Type} [Inhabited α] (a : Array α) (z : α) {h : Nat}
    (hh : h < a.size) : (a.push z)[h]! = a[h]! := by
  rw [getElem!_pos (a.push z) h (by rw [Array.size_push]; omega), getElem!_pos a h hh,
    Array.getElem_push_lt hh]

@[expose] def closStepAt (n : Nat) (gens gensInv : Array Table) (h : Nat) (st : ClosSt)
    (l : Nat) : ClosSt :=
  let z := conjT n gens[l]! gensInv[l]! st.1[h]!
  let kz := key n z
  if st.2.2.2.contains kz then st
  else (st.1.push z, st.2.1.push h, st.2.2.1.push l, kz :: st.2.2.2)

theorem closStep_eq_foldl (n : Nat) (gens gensInv : Array Table) (h : Nat) (st : ClosSt) :
    closStep n gens gensInv h st = (List.range gens.size).foldl (closStepAt n gens gensInv h) st :=
  rfl

theorem closStepAt_entry (n : Nat) (gens gensInv : Array Table) (h : Nat) (st : ClosSt)
    (l : Nat) (hh : h < st.1.size) :
    h < (closStepAt n gens gensInv h st l).1.size ∧
      (closStepAt n gens gensInv h st l).1[h]! = st.1[h]! := by
  unfold closStepAt
  dsimp only
  split
  · exact ⟨hh, rfl⟩
  · exact ⟨by simp only [Array.size_push]; omega, spec_getElem!_push _ _ hh⟩

theorem forIn_closStepAt (n : Nat) (gens gensInv : Array Table) (h : Nat) (y : Table)
    (Bin : Nat → NatSt → Id (ForInStep NatSt))
    (hBin : ∀ (l : Nat) (s : NatSt) (τ : ClosSt), SameSt s τ → h < τ.1.size → τ.1[h]! = y →
      ∃ s', Bin l s = ForInStep.yield s' ∧ SameSt s' (closStepAt n gens gensInv h τ l)) :
    ∀ (L : List Nat) (s : NatSt) (τ : ClosSt), SameSt s τ → h < τ.1.size → τ.1[h]! = y →
      SameSt (forIn L s Bin : Id NatSt) (L.foldl (closStepAt n gens gensInv h) τ) := by
  intro L
  induction L with
  | nil =>
    intro s τ hs _ _
    exact hs
  | cons l L ih =>
    intro s τ hs hh hy
    obtain ⟨s', hb, hs'⟩ := hBin l s τ hs hh hy
    obtain ⟨hh', hy'⟩ := closStepAt_entry n gens gensInv h τ l hh
    rw [List.forIn_cons, hb, List.foldl_cons]
    exact ih s' _ hs' hh' (hy'.trans hy)

theorem forIn_closLoop (n : Nat) (gens gensInv : Array Table)
    (B : Nat → NatSt → Id (ForInStep NatSt))
    (hB : ∀ (h : Nat) (s : NatSt) (σ : ClosSt), SameSt s σ →
      (h < σ.1.size → ∃ s', B h s = ForInStep.yield s' ∧
        SameSt s' (closStep n gens gensInv h σ)) ∧
      (¬ h < σ.1.size → B h s = ForInStep.done s)) :
    ∀ (f h : Nat) (s : NatSt) (σ : ClosSt), SameSt s σ →
      OutSt (forIn (List.range' h f) s B : Id NatSt) (closLoop n gens gensInv f h σ) := by
  intro f
  induction f with
  | zero =>
    intro h s σ hs
    obtain ⟨h1, h2, h3, -⟩ := hs
    show OutSt s (closLoop n gens gensInv 0 h σ)
    simp only [OutSt, closLoop, h1, h2, h3]
  | succ f ih =>
    intro h s σ hs
    rw [List.range'_succ, List.forIn_cons]
    by_cases hlt : h < σ.1.size
    · obtain ⟨s', hb, hs'⟩ := (hB h s σ hs).1 hlt
      rw [hb]
      show OutSt (forIn (List.range' (h + 1) f) s' B : Id NatSt)
        (closLoop n gens gensInv (f + 1) h σ)
      have hc : closLoop n gens gensInv (f + 1) h σ =
          closLoop n gens gensInv f (h + 1) (closStep n gens gensInv h σ) := by
        simp only [closLoop, hlt, ↓reduceIte]
      rw [hc]
      exact ih (h + 1) s' _ hs'
    · rw [(hB h s σ hs).2 hlt]
      show OutSt s (closLoop n gens gensInv (f + 1) h σ)
      obtain ⟨h1, h2, h3, -⟩ := hs
      simp only [OutSt, closLoop, hlt, ↓reduceIte, h1, h2, h3]

theorem forIn_range_eq_range' {β : Type} (m : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    forIn [:m] init f = forIn (List.range' 0 m) init f := by
  have hs : Std.Legacy.Range.size [:m] = m := by simp [Std.Legacy.Range.size]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', hs]

theorem closLoop_eq_forIn (n : Nat) (gens gensInv : Array Table) (cap : Nat)
    (B : Nat → NatSt → Id (ForInStep NatSt))
    (hB : ∀ (h : Nat) (s : NatSt) (σ : ClosSt), SameSt s σ →
      (h < σ.1.size → ∃ s', B h s = ForInStep.yield s' ∧
        SameSt s' (closStep n gens gensInv h σ)) ∧
      (¬ h < σ.1.size → B h s = ForInStep.done s))
    (s0 : NatSt) (σ0 : ClosSt) (h0 : SameSt s0 σ0) :
    closLoop n gens gensInv cap 0 σ0 =
      Id.run (forIn [:cap] s0 B >>= fun s => pure (s.2.1, s.2.2.1, s.2.2.2)) := by
  rw [forIn_range_eq_range']
  have key := forIn_closLoop n gens gensInv B hB cap 0 s0 σ0 h0
  unfold OutSt at key
  exact key.symm

theorem closStep_eq_foldl_range' (n : Nat) (gens gensInv : Array Table) (h : Nat) (st : ClosSt) :
    closStep n gens gensInv h st =
      (List.range' 0 gens.size).foldl (closStepAt n gens gensInv h) st := by
  rw [closStep_eq_foldl, List.range_eq_range']

theorem conjClosureL_eq_conjClosure (n : Nat) (gens gensInv : Array Table) (x : Table)
    (cap : Nat) :
    conjClosureL n gens gensInv x cap = conjClosure n gens gensInv x cap := by
  unfold conjClosureL conjClosure
  try dsimp only
  refine closLoop_eq_forIn n gens gensInv cap _ ?hB _ _ ?h0
  case h0 =>
    unfold SameSt
    refine ⟨rfl, rfl, rfl, fun k => ?_⟩
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, List.contains_cons,
      List.contains_nil, Bool.or_false, Bool.or_false, Bool.beq_comm]
  case hB =>
    intro h s σ hs
    have hs0 := hs
    obtain ⟨h1, h2, h3, h4⟩ := hs
    constructor
    · intro hlt
      have hlt' : h < s.2.1.size := by rw [h1]; exact hlt
      rw [if_pos hlt']
      refine ⟨_, rfl, ?_⟩
      · simp only [Prod.eta]
        rw [forIn_range_eq_range', closStep_eq_foldl_range']
        refine forIn_closStepAt n gens gensInv h (s.2.1[h]!) _ ?_ _ _ _ ?_ ?_ ?_
        · intro l t τ ht hτh hτy
          obtain ⟨ht1, ht2, ht3, ht4⟩ := ht
          rw [← hτy]
          try dsimp only
          by_cases hc : t.1.contains (key n (conjT n gens[l]! gensInv[l]! τ.1[h]!)) = true
          · refine ⟨t, ?_, ?_⟩
            · have hn : ¬ ((!t.1.contains (key n (conjT n gens[l]! gensInv[l]! τ.1[h]!)))
                  = true) := by simp [hc]
              rw [if_neg hn]
              rfl
            · unfold closStepAt
              try dsimp only
              have hc' : τ.2.2.2.contains (key n (conjT n gens[l]! gensInv[l]! τ.1[h]!))
                  = true := by
                rw [← ht4]
                exact hc
              rw [if_pos hc']
              exact ⟨ht1, ht2, ht3, ht4⟩
          · have hp : (!t.1.contains (key n (conjT n gens[l]! gensInv[l]! τ.1[h]!)))
                = true := by simpa using hc
            rw [if_pos hp]
            refine ⟨_, rfl, ?_⟩
            · unfold closStepAt
              try dsimp only
              have hc' : ¬ (τ.2.2.2.contains (key n (conjT n gens[l]! gensInv[l]! τ.1[h]!))
                  = true) := by
                rw [← ht4]
                exact hc
              rw [if_neg hc']
              unfold SameSt
              refine ⟨?_, ?_, ?_, ?_⟩
              · try dsimp only
                rw [ht1]
              · try dsimp only
                rw [ht2]
              · try dsimp only
                rw [ht3]
              · intro k
                try dsimp only
                rw [Std.HashSet.contains_insert, List.contains_cons, ← ht4 k]
                rw [Bool.beq_comm]
        · exact hs0
        · exact hlt
        · rw [h1]
    · intro hlt
      have hlt' : ¬ h < s.2.1.size := by rw [h1]; exact hlt
      rw [if_neg hlt']
      rfl

end CFSG.KC.LocalComp.Spec

end
