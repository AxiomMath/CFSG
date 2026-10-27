module

public import CFSG.ClassicalInvolution.Phan.PhanS0Graph

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q

open SimpleGraph CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanB3.S

variable {V : Type*} {G : SimpleGraph V}

@[expose] def QN (G : SimpleGraph V) (a b c d : V) : Prop :=
  ∀ (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a),
    CycleHomotopic (triWalks G)
      (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a) .nil

theorem tri_null {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) :
    CycleHomotopic (triWalks G) (.cons hxy (.cons hyz (.cons hzx .nil)) : G.Walk x x) .nil :=
  cycleHomotopic_of_mem _ rfl

theorem quadNull_iff : QuadNull G ↔ ∀ a b c d : V, QN G a b c d :=
  ⟨fun h a b c d hab hbc hcd hda => h a b c d hab hbc hcd hda,
    fun h a b c d hab hbc hcd hda => h a b c d hab hbc hcd hda⟩

theorem QN.of_apex {a b c d z : V} (haz : G.Adj a z) (hbz : G.Adj b z) (hcz : G.Adj c z)
    (hdz : G.Adj d z) : QN G a b c d := by
  intro hab hbc hcd hda
  refine cycleHomotopic_cone_nil (triWalks G) (e := z)
    (fun x y => G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) ?_ _ haz ?_
  · rintro x y ⟨hxy, hxz, hyz⟩
    exact ⟨hxy, hxz, hyz, tri_null _ _ _⟩
  · intro d' hd'
    simp only [Walk.darts_cons, Walk.darts_nil, List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl | rfl | rfl
    · exact ⟨hab, haz, hbz⟩
    · exact ⟨hbc, hbz, hcz⟩
    · exact ⟨hcd, hcz, hdz⟩
    · exact ⟨hda, hdz, haz⟩

theorem QN.move {a b c d e : V} (hae : G.Adj a e) (hbe : G.Adj b e) (hce : G.Adj c e)
    (h : QN G a e c d) : QN G a b c d := by
  intro hab hbc hcd hda
  have hcone : CycleHomotopic (triWalks G) (.cons hab (.cons hbc .nil) : G.Walk a c)
      (.cons hae (.cons hce.symm .nil)) := by
    refine cycleHomotopic_cone (triWalks G) (e := e)
      (fun x y => (x = a ∧ y = b) ∨ (x = b ∧ y = c)) ?_ _ hae hce ?_
    · rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hab, hae, hbe, tri_null _ _ _⟩
      · exact ⟨hbc, hbe, hce, tri_null _ _ _⟩
    · intro d' hd'
      simp only [Walk.darts_cons, Walk.darts_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hd'
      rcases hd' with rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
  have := (hcone.append_right (.cons hcd (.cons hda .nil) : G.Walk c a))
  simp only [Walk.cons_append, Walk.nil_append] at this
  exact this.trans (h hae hce.symm hcd hda)

theorem QN.rotate {a b c d : V} (h : QN G a b c d) : QN G b c d a := by
  intro hbc hcd hda hab
  refine cycleHomotopic_nil_of_conj (E := triWalks G) (.cons hab .nil : G.Walk a b) _ ?_
  have h1 := (h hab hbc hcd hda).append (cycleHomotopic_cons_cons_nil (triWalks G) hab)
  simpa using h1

theorem QN.move_fourth {a b c d e : V} (hae : G.Adj a e) (hce : G.Adj c e) (hde : G.Adj d e)
    (h : QN G a b c e) : QN G a b c d :=
  (QN.move (a := c) (b := d) (c := a) (d := b) (e := e) hce hde hae h.rotate.rotate).rotate.rotate

theorem QN.of_eq_diag {a b c : V} : QN G a b c b := by
  intro hab hbc hcd hda
  have h1 := cycleHomotopic_backtrack (triWalks G) (.cons hab .nil : G.Walk a b)
    (.cons hab.symm .nil : G.Walk b a) hbc
  have h2 : CycleHomotopic (triWalks G) (.cons hab (.cons hab.symm .nil) : G.Walk a a) .nil :=
    cycleHomotopic_cons_cons_nil (triWalks G) hab
  simp only [Walk.cons_append, Walk.nil_append] at h1
  exact h1.symm.trans h2

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q
