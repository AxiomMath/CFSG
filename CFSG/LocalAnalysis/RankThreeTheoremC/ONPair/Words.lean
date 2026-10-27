module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.ModelCheck
public import CFSG.RankThree.Native.ONSevenRestrict
public import CFSG.Monster.B.Mathieu.SylowSound
public import CFSG.RankThree.Native.ONSevenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.RankThree.Native

theorem map_evalWord {G H : Type*} [Group G] [Group H] (f : G →* H) {S : Type*} (ι : S → G)
    (w : List (S × Bool)) :
    f (Quiver.SchreierGraph.evalWord ι w) = Quiver.SchreierGraph.evalWord (f ∘ ι) w := by
  induction w with
  | nil => simp [Quiver.SchreierGraph.evalWord_nil]
  | cons l w ih =>
    obtain ⟨s, b⟩ := l
    cases b
    · rw [Quiver.SchreierGraph.evalWord_cons_false, Quiver.SchreierGraph.evalWord_cons_false,
        map_mul, map_inv, ih]
      rfl
    · rw [Quiver.SchreierGraph.evalWord_cons_true, Quiver.SchreierGraph.evalWord_cons_true,
        map_mul, ih]
      rfl

theorem evalWord_mem {G : Type*} [Group G] {K : Subgroup G} {S : Type*} {ι : S → G}
    (h : ∀ s, ι s ∈ K) (w : List (S × Bool)) : Quiver.SchreierGraph.evalWord ι w ∈ K :=
  (Subgroup.closure_le K).2 (by rintro _ ⟨s, rfl⟩; exact h s)
    (Quiver.SchreierGraph.evalWord_mem_closure ι w)

section Model

@[expose] noncomputable def hgen (h : ℕ) : Equiv.Perm (Fin N) :=
  if h = 0 then evalS h1Word else if h = 1 then evalS h2Word else 1

@[expose] noncomputable def hval (w : List ℤ) : Equiv.Perm (Fin N) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 2 => hgen h) (ptoLetters 2 w)

theorem hgen_mem (h : ℕ) : hgen h ∈ Pv := by
  unfold hgen
  split_ifs
  · exact evalS_mem _
  · exact evalS_mem _
  · exact one_mem _

theorem hval_mem (w : List ℤ) : hval w ∈ Pv :=
  evalWord_mem (ι := fun h : Fin 2 => hgen h) (fun h => hgen_mem h) _

theorem hgen_zero : hgen 0 = evalS h1Word := by simp [hgen]

theorem hgen_one : hgen 1 = evalS h2Word := by simp [hgen]

end Model

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
