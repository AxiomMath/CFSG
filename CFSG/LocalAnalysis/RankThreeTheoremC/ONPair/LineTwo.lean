module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.Alpha
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.NQRelab
import Mathlib.Tactic.FinCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier CFSG.ONSchreier.Native
open CFSG.Sporadic.HNSchreier (gStrong gStrong_of_lt)

theorem evalWord_gStrong_eq_nqEv2 {G : Type*} [Group G] (x0 x1 : G) (W : Array (List ℤ))
    {w : List ℤ} (hw : plettersOK 2 w = true) :
    Quiver.SchreierGraph.evalWord (fun h : Fin 7 => gStrong [x0, x1] W h) (ptoLetters 7 w) =
      nqEv2 x0 x1 w := by
  rw [evalWord_le_two (by norm_num) (gStrong [x0, x1] W) hw,
    gStrong_of_lt [x0, x1] W (j := 0) (by simp), gStrong_of_lt [x0, x1] W (j := 1) (by simp)]
  rfl

theorem map_nqEv2 {G H : Type*} [Group G] [Group H] (f : G →* H) (a b : G) (w : List ℤ) :
    f (nqEv2 a b w) = nqEv2 (f a) (f b) w := by
  unfold nqEv2
  rw [map_evalWord]
  congr 1
  funext h
  simp only [Function.comp_apply]
  split_ifs <;> rfl

section Lines


theorem lineAct_pvEval_nq {w : List ℤ} (hw : plettersOK 2 w = true) :
    lineAct (pvEval w) = nqRho w := by
  rw [lineAct_pvEval]
  exact evalWord_gStrong_eq_nqEv2 d0 d1 Data.strongWords hw

theorem lineAct_hgenP_nq : lineAct (hgenP 0) = nqRho h1Word ∧ lineAct (hgenP 1) = nqRho h2Word := by
  have e0 : hgenP 0 = pvEval h1Word := Subtype.ext hgen_zero
  have e1 : hgenP 1 = pvEval h2Word := Subtype.ext hgen_one
  rw [e0, e1]
  exact ⟨lineAct_pvEval_nq (by decide), lineAct_pvEval_nq (by decide)⟩

theorem lineAct_hval_nq (w : List ℤ) : lineAct ⟨hval w, hval_mem w⟩ = nqSig w := by
  rw [hP_eq, map_evalWord]
  unfold nqSig nqEv2
  congr 1
  funext h
  fin_cases h
  · exact lineAct_hgenP_nq.1
  · exact lineAct_hgenP_nq.2

@[expose] noncomputable def lineTwo : Fin nL := lineAct (pvEval u2Word) 0

theorem lineTwo_eq_nqL2 : lineTwo = nqL2 := by
  unfold lineTwo nqL2
  rw [lineAct_pvEval_nq (by decide)]

theorem lineAct_alphaWordA : lineAct (pvEval alphaWordA) = nqAP :=
  lineAct_pvEval_nq (by decide)


@[expose] noncomputable def lineActA : Pv →* Equiv.Perm (Fin nL) :=
  lineAct.comp (alphaP : Pv →* Pv)

theorem lineActA_apply (g : Pv) : lineActA g = lineAct (alphaP g) := rfl

theorem lineActA_a0 : lineActA ⟨a0, a0_mem⟩ = lineAct (pvEval alphaWordA) := by
  rw [lineActA_apply, alphaP_a0]

theorem lineActA_a1 : lineActA ⟨a1, a1_mem⟩ = d1 := by
  rw [lineActA_apply, alphaP_a1, lineAct_a1]

theorem lineActA_pvEval (w : List ℤ) :
    lineActA (pvEval w) = Quiver.SchreierGraph.evalWord
      (fun h : Fin 7 => gStrong [lineAct (pvEval alphaWordA), d1] Data.strongWords h)
      (ptoLetters 7 w) := by
  rw [map_pvEval, lineActA_a0, lineActA_a1]

theorem lineActA_pvEval_nq {w : List ℤ} (hw : plettersOK 2 w = true) :
    lineActA (pvEval w) = nqRhoA w := by
  rw [lineActA_pvEval, evalWord_gStrong_eq_nqEv2 _ _ _ hw, lineAct_alphaWordA]
  rfl

theorem lineActA_hgenP_nq :
    lineActA (hgenP 0) = nqRhoA h1Word ∧ lineActA (hgenP 1) = nqRhoA h2Word := by
  have e0 : hgenP 0 = pvEval h1Word := Subtype.ext hgen_zero
  have e1 : hgenP 1 = pvEval h2Word := Subtype.ext hgen_one
  rw [e0, e1]
  exact ⟨lineActA_pvEval_nq (by decide), lineActA_pvEval_nq (by decide)⟩

theorem lineActA_hval_nq (w : List ℤ) : lineActA ⟨hval w, hval_mem w⟩ = nqSigA w := by
  rw [hP_eq, map_evalWord]
  unfold nqSigA nqEv2
  congr 1
  funext h
  fin_cases h
  · exact lineActA_hgenP_nq.1
  · exact lineActA_hgenP_nq.2

@[expose] noncomputable def G2 : Subgroup Pv := (lineStab lineTwo).comap (alphaP : Pv →* Pv)

theorem mem_G2 {g : Pv} : g ∈ G2 ↔ lineActA g lineTwo = lineTwo := Iff.rfl

end Lines

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
