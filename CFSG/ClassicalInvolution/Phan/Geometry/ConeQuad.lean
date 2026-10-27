module

public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycleMoves
public import CFSG.Monster.B.Recog.GenericWalkHomotopy
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ClassicalInvolution.Phan

open SimpleGraph

theorem cycleHomotopic_quadWalk_of_eq_third {V : Type*} {G : SimpleGraph V}
    (E : ∀ x : V, Set (G.Walk x x)) {a b d : V} (hab : G.Adj a b) (hba : G.Adj b a)
    (had : G.Adj a d) (hda : G.Adj d a) :
    CycleHomotopic E (quadWalk hab hba had hda) .nil := by
  classical
  have h1 : CycleHomotopic E (.cons hab (.cons hba .nil) : G.Walk a a) .nil := by
    simpa [Subsingleton.elim hba hab.symm] using cycleHomotopic_cons_cons_nil E hab
  have h2 : CycleHomotopic E (.cons had (.cons hda .nil) : G.Walk a a) .nil := by
    simpa [Subsingleton.elim hda had.symm] using cycleHomotopic_cons_cons_nil E had
  simpa [quadWalk] using h1.append h2

theorem cycleHomotopic_quadWalk_of_eq_fourth {V : Type*} {G : SimpleGraph V}
    (E : ∀ x : V, Set (G.Walk x x)) {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcb : G.Adj c b) (hba : G.Adj b a) :
    CycleHomotopic E (quadWalk hab hbc hcb hba) .nil := by
  classical
  have h1 : CycleHomotopic E (quadWalk hab hbc hcb hba)
      (.cons hab (.cons hba .nil) : G.Walk a a) := by
    have h := cycleHomotopic_backtrack E
      (.cons hab .nil : G.Walk a b) (.cons hba .nil : G.Walk b a) hbc
    simpa [quadWalk, Subsingleton.elim hcb hbc.symm] using h.symm
  have h2 : CycleHomotopic E (.cons hab (.cons hba .nil) : G.Walk a a) .nil := by
    simpa [Subsingleton.elim hba hab.symm] using cycleHomotopic_cons_cons_nil E hab
  exact h1.trans h2

theorem cycleHomotopic_quadWalk_of_chord {V : Type*} {G : SimpleGraph V}
    (E : ∀ x : V, Set (G.Walk x x)) (h3 : NullLen E 3)
    {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hchord : G.Adj a c) : CycleHomotopic E (quadWalk hab hbc hcd hda) .nil := by
  classical
  have habc : CycleHomotopic E (triWalk hab hbc hchord.symm) .nil := h3 _ rfl
  have hacd : CycleHomotopic E (triWalk hchord hcd hda) .nil := h3 _ rfl
  have hdetour : CycleHomotopic E (quadWalk hab hbc hcd hda)
      ((triWalk hab hbc hchord.symm).append (triWalk hchord hcd hda)) := by
    have h := cycleHomotopic_backtrack E
      (.cons hab (.cons hbc .nil) : G.Walk a c)
      (.cons hcd (.cons hda .nil) : G.Walk c a) hchord.symm
    simpa [triWalk, quadWalk] using h
  exact hdetour.trans (habc.append hacd)

variable {V : Type*} {G : SimpleGraph V} (E : ∀ x : V, Set (G.Walk x x))

theorem cycleHomotopic_quad_of_preconnected (h3 : NullLen E 3) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hcone : (G.induce (G.neighborSet a ∩ G.neighborSet c)).Preconnected) :
    CycleHomotopic E (quadWalk hab hbc hcd hda) .nil := by
  classical
  let N : Set V := G.neighborSet a ∩ G.neighborSet c
  have hcone' : (G.induce N).Preconnected := by simpa [N] using hcone
  let hbN : b ∈ N := ⟨hab, hbc.symm⟩
  let hdN : d ∈ N := ⟨hda.symm, hcd⟩
  obtain ⟨w⟩ := hcone' ⟨b, hbN⟩ ⟨d, hdN⟩
  have hres : CycleHomotopic E
      (quadWalk (show G.Adj a b from hbN.1) (show G.Adj b c from hbN.2.symm)
        (show G.Adj c d from hdN.2) (show G.Adj d a from hdN.1.symm)) .nil :=
    SimpleGraph.Walk.rec
      (motive := fun (u v : N) _ => CycleHomotopic E
        (quadWalk (show G.Adj a u.1 from u.2.1) (show G.Adj u.1 c from u.2.2.symm)
          (show G.Adj c v.1 from v.2.2) (show G.Adj v.1 a from v.2.1.symm)) .nil)
      (fun {u : N} =>
        cycleHomotopic_quadWalk_of_eq_fourth E u.2.1 u.2.2.symm u.2.2 u.2.1.symm)
      (fun {x y z : N}
          (h : (G.induce N).Adj x y)
          (_ : (G.induce N).Walk y z)
          (ih : CycleHomotopic E
            (quadWalk (show G.Adj a y.1 from y.2.1) (show G.Adj y.1 c from y.2.2.symm)
              (show G.Adj c z.1 from z.2.2) (show G.Adj z.1 a from z.2.1.symm)) .nil) => by
        have hxy : G.Adj x.1 y.1 := SimpleGraph.induce_adj.mp h
        have hchord : CycleHomotopic E
            (quadWalk (show G.Adj a x.1 from x.2.1) (show G.Adj x.1 c from x.2.2.symm)
              (show G.Adj c y.1 from y.2.2) (show G.Adj y.1 a from y.2.1.symm)) .nil := by
          have h0 : CycleHomotopic E
              (quadWalk (show G.Adj x.1 c from x.2.2.symm)
                (show G.Adj c y.1 from y.2.2) (show G.Adj y.1 a from y.2.1.symm)
                (show G.Adj a x.1 from x.2.1)) .nil :=
            cycleHomotopic_quadWalk_of_chord E h3 x.2.2.symm y.2.2 y.2.1.symm x.2.1 hxy
          exact cycleHomotopic_quad_rotate E y.2.1.symm x.2.1 x.2.2.symm y.2.2
            (cycleHomotopic_quad_rotate E y.2.2 y.2.1.symm x.2.1 x.2.2.symm
              (cycleHomotopic_quad_rotate E x.2.2.symm y.2.2 y.2.1.symm x.2.1 h0))
        exact cycleHomotopic_quad_trans E x.2.1 x.2.2.symm y.2.2 y.2.1.symm z.2.2 z.2.1.symm
          hchord ih)
      w
  simpa only [Subsingleton.elim hbN.1 hab, Subsingleton.elim hbN.2.symm hbc,
    Subsingleton.elim hdN.2 hcd, Subsingleton.elim hdN.1.symm hda] using hres

variable (G) in
theorem nullLen_three_homotopic :
    NullLen (fun x => {c : G.Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil}) 3 := by
  intro u p hp
  match u, p, hp with
  | _, .nil, hp => simp at hp
  | _, .cons _ .nil, hp => simp at hp
  | _, .cons _ (.cons _ .nil), hp => simp at hp
  | a, .cons h₁ (.cons h₂ (.cons h₃ .nil)), _ =>
    refine cycleHomotopic_of_mem _ ?_
    have htri : CFSG.Monster.B.Recog.Homotopic
        (.cons h₁ (.cons h₂ (.cons h₃ .nil)) : G.Walk a a) .nil := by
      simpa using (CFSG.Monster.B.Recog.homotopic_triangle
        (p := (SimpleGraph.Walk.nil : G.Walk a a))
        (q := (SimpleGraph.Walk.nil : G.Walk a a)) h₁ h₂ h₃).symm
    exact htri
  | _, .cons _ (.cons _ (.cons _ (.cons _ _))), hp =>
    simp only [Walk.length_cons] at hp
    omega

theorem triangulable_of_cycleTrivial
    (h : CycleTrivial (fun x => {c : G.Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil})) :
    CFSG.Monster.B.Recog.Triangulable G := by
  intro u p
  have key : ∀ {u v : V} {p q : G.Walk u v},
      CycleHomotopic (fun x => {c : G.Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil}) p q →
      CFSG.Monster.B.Recog.Homotopic p q := by
    intro u v p q hpq
    induction hpq with
    | rel p q hmove =>
      cases hmove with
      | backtrack a b e =>
        simpa using CFSG.Monster.B.Recog.homotopic_backtrack a b e
      | elem a b c hc =>
        have hc' : CFSG.Monster.B.Recog.Homotopic (c.append b) b := by
          simpa using
            (show CFSG.Monster.B.Recog.Homotopic c .nil from hc).append_right b
        simpa using ((CFSG.Monster.B.Recog.Homotopic.refl a).append hc').symm
    | refl p => exact CFSG.Monster.B.Recog.Homotopic.refl p
    | symm p q _ ih => exact ih.symm
    | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact key (h u p)

end CFSG.ClassicalInvolution.Phan
