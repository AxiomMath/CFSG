module

public import Certificates.Data.Seitz77L34V1Act

public section

namespace Certificates.Seitz77L34

open CFSG.PSL3Four.Native

@[expose] def v1Img (EF : Array Tab) (r : Tab) : Tab :=
  EF.map fun f => posOf (indexOf EF) EF (conjTab 42 r (invTab 42 r) f)

@[expose] def v1Ok (EF : Array Tab) (r : Tab) : Bool :=
  allBelow EF.size fun i => (v1Img EF r)[i]! < EF.size &&
    EF[(v1Img EF r)[i]!]! == conjTab 42 r (invTab 42 r) EF[i]!

@[expose] def v1Step (EF : Array Tab) (s : Std.HashMap Tab Unit × Array Tab) (r : Tab) :
    Std.HashMap Tab Unit × Array Tab :=
  if v1Ok EF r = true then
    if (!s.1.contains (v1Img EF r)) = true then (s.1.insert (v1Img EF r) (), s.2.push (v1Img EF r))
    else s
  else s

theorem v1Acts_eq (EF ER : Array Tab) : v1Acts EF ER = (ER.foldl (v1Step EF) (∅, #[])).2 := by
  unfold v1Acts
  simp only [Id.run]
  have hb : (fun (r : Tab) (s : Std.HashMap Tab Unit × Array Tab) =>
      if v1Ok EF r = true then
        if (!s.fst.contains (v1Img EF r)) = true then
          (pure (ForInStep.yield (s.fst.insert (v1Img EF r) (), s.snd.push (v1Img EF r))) :
            Id (ForInStep (Std.HashMap Tab Unit × Array Tab)))
        else pure (ForInStep.yield (s.fst, s.snd))
      else pure (ForInStep.yield (s.fst, s.snd))) =
      fun r s => pure (ForInStep.yield (v1Step EF s r)) := by
    funext r s
    unfold v1Step
    by_cases h1 : v1Ok EF r = true
    · by_cases h2 : (!s.fst.contains (v1Img EF r)) = true
      · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]
      · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
    · rw [if_neg h1, if_neg h1]
  unfold v1Ok v1Img at hb
  rw [hb, Array.forIn_pure_yield_eq_foldl]
  rfl

theorem mem_v1Acts (EF ER : Array Tab) (x : Tab) :
    x ∈ v1Acts EF ER ↔ ∃ r ∈ ER, v1Ok EF r = true ∧ v1Img EF r = x := by
  rw [v1Acts_eq]
  have key := Array.foldl_induction (as := ER) (f := v1Step EF) (init := (∅, #[]))
    (fun i (s : Std.HashMap Tab Unit × Array Tab) =>
      (∀ y, s.1.contains y = true ↔ y ∈ s.2) ∧
        ∀ y, y ∈ s.2 ↔ ∃ j, ∃ h : j < ER.size, j < i ∧ v1Ok EF ER[j] = true ∧ v1Img EF ER[j] = y)
    ⟨fun y => by simp, fun y => by simp⟩ (fun i s hs => by
      obtain ⟨h1, h2⟩ := hs
      unfold v1Step
      by_cases hok : v1Ok EF ER[i] = true
      · by_cases hc : s.1.contains (v1Img EF ER[i]) = true
        · have hnc : ¬((!s.1.contains (v1Img EF ER[i])) = true) := by rw [hc]; decide
          rw [if_pos hok, if_neg hnc]
          refine ⟨h1, fun y => ?_⟩
          rw [h2]
          constructor
          · rintro ⟨j, hj, hji, h⟩
            exact ⟨j, hj, by omega, h⟩
          · rintro ⟨j, hj, hji, hok', he⟩
            by_cases e : j = i.val
            · subst e
              rw [← he]
              exact (h2 _).1 ((h1 _).1 hc)
            · exact ⟨j, hj, by omega, hok', he⟩
        · have hnc : (!s.1.contains (v1Img EF ER[i])) = true := by
            cases h : s.1.contains (v1Img EF ER[i])
            · rfl
            · exact absurd h hc
          rw [if_pos hok, if_pos hnc]
          refine ⟨fun y => ?_, fun y => ?_⟩
          · rw [Std.HashMap.contains_insert, Array.mem_push, Bool.or_eq_true, h1, beq_iff_eq]
            exact ⟨fun h => h.elim (fun e => Or.inr e.symm) Or.inl,
              fun h => h.elim Or.inr (fun e => Or.inl e.symm)⟩
          · rw [Array.mem_push, h2]
            constructor
            · rintro (⟨j, hj, hji, h⟩ | e)
              · exact ⟨j, hj, by omega, h⟩
              · exact ⟨i.val, i.isLt, by omega, hok, e.symm⟩
            · rintro ⟨j, hj, hji, hok', he⟩
              by_cases e : j = i.val
              · subst e
                exact Or.inr he.symm
              · exact Or.inl ⟨j, hj, by omega, hok', he⟩
      · rw [if_neg hok]
        refine ⟨h1, fun y => ?_⟩
        rw [h2]
        constructor
        · rintro ⟨j, hj, hji, h⟩
          exact ⟨j, hj, by omega, h⟩
        · rintro ⟨j, hj, hji, hok', he⟩
          by_cases e : j = i.val
          · subst e
            exact absurd hok' hok
          · exact ⟨j, hj, by omega, hok', he⟩)
  rw [key.2 x]
  constructor
  · rintro ⟨j, hj, -, hok, he⟩
    exact ⟨ER[j], Array.getElem_mem hj, hok, he⟩
  · rintro ⟨r, hr, hok, he⟩
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hr
    exact ⟨j, hj, hj, hok, he⟩

end Certificates.Seitz77L34

end
