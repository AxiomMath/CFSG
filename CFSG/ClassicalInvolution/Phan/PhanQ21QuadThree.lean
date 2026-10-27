module

public import CFSG.ClassicalInvolution.Phan.PhanQ18Machinery

public section

namespace CFSG.ClassicalInvolution.PhanQ

open SimpleGraph CFSG.ClassicalInvolution.Phan

section Quad

variable {V : Type*} {G : SimpleGraph V}

theorem triWalks_null {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) :
    CycleHomotopic (triWalks G) (.cons hxy (.cons hyz (.cons hzx .nil)) : G.Walk x x) .nil :=
  cycleHomotopic_of_mem (triWalks G) (by simp [triWalks])

theorem cycleHomotopic_quad_diag {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) (hbd : G.Adj b d) :
    CycleHomotopic (triWalks G)
      (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a) .nil := by
  have hT : CycleHomotopic (triWalks G)
      (.cons hbd (.cons hcd.symm (.cons hbc.symm .nil)) : G.Walk b b) .nil :=
    triWalks_null hbd hcd.symm hbc.symm
  have hrep := cycleHomotopic_replace_edge (triWalks G) hbd hbc hcd.symm hT
  have h1 : CycleHomotopic (triWalks G)
      (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a)
      (.cons hab (.cons hbd (.cons hda .nil))) := by
    have := (hrep.symm.append_right (.cons hda .nil)).append_left (.cons hab .nil)
    simpa using this
  exact h1.trans (triWalks_null hab hbd hda)

theorem cycleHomotopic_quad_common {a b c d e : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) (hae : G.Adj a e) (hbe : G.Adj b e) (hce : G.Adj c e)
    (hde : G.Adj d e) :
    CycleHomotopic (triWalks G)
      (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a) .nil := by
  refine cycleHomotopic_cone_nil (triWalks G) (e := e)
    (fun x y => G.Adj x y ∧ G.Adj x e ∧ G.Adj y e) ?_ _ hae ?_
  · rintro x y ⟨hxy, hxe, hye⟩
    exact ⟨hxy, hxe, hye, triWalks_null hxy hye hxe.symm⟩
  · intro d' hd'
    simp only [Walk.darts_cons, Walk.darts_nil, List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl | rfl | rfl
    · exact ⟨hab, hae, hbe⟩
    · exact ⟨hbc, hbe, hce⟩
    · exact ⟨hcd, hce, hde⟩
    · exact ⟨hda, hde, hae⟩

theorem cycleHomotopic_path_swap {a c x y : V} (hax : G.Adj a x) (hxc : G.Adj x c)
    (hay : G.Adj a y) (hyc : G.Adj y c) (hxy : G.Adj x y) :
    CycleHomotopic (triWalks G) (.cons hax (.cons hxc .nil) : G.Walk a c)
      (.cons hay (.cons hyc .nil)) := by
  refine cycleHomotopic_of_append_reverse _ ?_
  have := cycleHomotopic_quad_diag hax hxc hyc.symm hay.symm hxy
  simpa using this

end Quad

end CFSG.ClassicalInvolution.PhanQ
