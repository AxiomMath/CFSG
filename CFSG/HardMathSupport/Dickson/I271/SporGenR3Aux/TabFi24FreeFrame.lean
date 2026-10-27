module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24Dec
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24FreeGen
public import CFSG.GH74.QTGen4.Recog.G23.Words
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestCover
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24FreeFacts
public import Certificates.Certificate17568
public import Certificates.Data.CFSGNative.Timmesfeld.Fi24Free

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
open CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest (evalW lift_mk_eq_evalW)
open CFSG.GH74.QTGen4.Recog.G23 (SatisfiesG23Words g23Words)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

set_option linter.unusedSectionVars false

theorem frWc0_lt : ∀ l ∈ frWc0, l < letters.size := by
  rw [letters_size_eq]
  decide

theorem frWc1_lt : ∀ l ∈ frWc1, l < letters.size := by
  rw [letters_size_eq]
  decide

@[expose] def epsW (i : Fin 6) : List ℕ := frEps[i.val]!

@[expose] noncomputable def epsJ (i : Fin 6) : J := wordElt (epsW i)

@[expose] noncomputable def cA : Fin 306936 := frA

@[expose] noncomputable def cB : Fin 306936 := frB

noncomputable def u2 : J := (exists_jR_of_mem (cls_mul_cls_mem_JR cA cB)).choose

theorem jR_u2 : jR u2 = cls cA * cls cB :=
  (exists_jR_of_mem (cls_mul_cls_mem_JR cA cB)).choose_spec

@[expose] noncomputable def xJ : J := s0 * u2

theorem cA_val : cA.val = frPt ctx frWc0 := by
  unfold cA frA frPt
  rw [smul_val_of_rep (rep_wordTab frWc0 frWc0_lt)]

theorem cB_val : cB.val = frPt ctx frWc1 := by
  unfold cB frB frPt
  rw [smul_val_of_rep (rep_wordTab frWc1 frWc1_lt)]

structure FrameFacts : Prop where
  nc_01 : ¬Cm pt0 pt1
  nc_AB : ¬Cm cA cB
  c_0A : Cm pt0 cA
  c_0B : Cm pt0 cB
  c_1A : Cm pt1 cA
  c_1B : Cm pt1 cB
  disj_A : cA ≠ pt0 ∧ cA ≠ pt1 ∧ cA ≠ third pt0 pt1
  disj_B : cB ≠ pt0 ∧ cB ≠ pt1 ∧ cB ≠ third pt0 pt1
  disj_M : third cA cB ≠ pt0 ∧ third cA cB ≠ pt1 ∧ third cA cB ≠ third pt0 pt1
  conj : wordElt frG1 * wordElt [2] = xJ * wordElt frG1
  eps_fix : ∀ i : Fin 6, epsJ i • pt0 = pt0 ∧ epsJ i • pt1 = pt1 ∧ epsJ i • cA = cA ∧
    epsJ i • cB = cB
  eps_rel : SatisfiesG23Words epsJ
  eps_ne : ∃ i, epsJ i ≠ 1

section Geometry

theorem prod_smul_fix {a b q : Fin 306936} {w : J} (hw : jR w = cls a * cls b) (ha : Cm q a)
    (hb : Cm q b) : w • q = q := by
  rw [smul_eq_iff_commute, hw]
  exact (Commute.mul_right (show Commute (cls q) (cls a) from ha)
    (show Commute (cls q) (cls b) from hb)).eq.symm

theorem s0_smul_cB (hF : FrameFacts) : s0 • cB = cB :=
  prod_smul_fix jR_s0 hF.c_0B.symm hF.c_1B.symm

theorem u2_smul_pt0 (hF : FrameFacts) : u2 • pt0 = pt0 := prod_smul_fix jR_u2 hF.c_0A hF.c_0B

theorem u2_smul_pt1 (hF : FrameFacts) : u2 • pt1 = pt1 := prod_smul_fix jR_u2 hF.c_1A hF.c_1B

theorem fr_s0_pt0 (hF : FrameFacts) : s0 • pt0 = pt1 := line_smul_fst hF.nc_01 jR_s0

theorem fr_s0_pt1 (hF : FrameFacts) : s0 • pt1 = third pt0 pt1 := line_smul_snd hF.nc_01 jR_s0

theorem u2_smul_cA (hF : FrameFacts) : u2 • cA = cB := line_smul_fst hF.nc_AB jR_u2

theorem u2_smul_cB (hF : FrameFacts) : u2 • cB = third cA cB := line_smul_snd hF.nc_AB jR_u2

theorem u2_smul_m2 (hF : FrameFacts) : u2 • third cA cB = cA := line_smul_third hF.nc_AB jR_u2

theorem s0_mul_u2 (hF : FrameFacts) : s0 * u2 = u2 * s0 := by
  apply CFSG.Sporadic.Fi24.jR_injective
  rw [map_mul, map_mul, jR_s0, jR_u2]
  exact (Commute.mul_left (Commute.mul_right (show Commute (cls pt0) (cls cA) from hF.c_0A)
    (show Commute (cls pt0) (cls cB) from hF.c_0B))
    (Commute.mul_right (show Commute (cls pt1) (cls cA) from hF.c_1A)
    (show Commute (cls pt1) (cls cB) from hF.c_1B))).eq

theorem xJ_smul (p : Fin 306936) : xJ • p = s0 • u2 • p := mul_smul s0 u2 p

theorem xJ_smul_pt0 (hF : FrameFacts) : xJ • pt0 = pt1 := by
  rw [xJ_smul, u2_smul_pt0 hF, fr_s0_pt0 hF]

theorem xJ_smul_pt1 (hF : FrameFacts) : xJ • pt1 = third pt0 pt1 := by
  rw [xJ_smul, u2_smul_pt1 hF, fr_s0_pt1 hF]

theorem xJ_smul_cA (hF : FrameFacts) : xJ • cA = cB := by
  rw [xJ_smul, u2_smul_cA hF, s0_smul_cB hF]

end Geometry

theorem clsPt_m1 : clsPt ctx 0 305530 = (third pt0 pt1).val := clsPt_eq_smul pt0 pt1

theorem clsPt_m2 : clsPt ctx cA.val cB.val = (third cA cB).val := clsPt_eq_smul cA cB

theorem jR_xJ : jR xJ = xFr := by
  unfold xJ
  rw [map_mul, jR_s0, jR_u2]
  rfl

section Parts

theorem frame_parts : FreeFrameFacts := Certificates.certificate17568

theorem frame_facts : FrameFacts := by
  have hF := frame_parts
  refine ⟨hF.nc_01, hF.nc_AB, hF.c_0A, hF.c_0B, hF.c_1A, hF.c_1B, hF.disj_A, hF.disj_B,
    hF.disj_M, ?_, hF.eps_fix, hF.eps_rel, hF.eps_ne⟩
  apply CFSG.Sporadic.Fi24.jR_injective
  rw [hF.conj, map_mul, jR_xJ]

end Parts

end CFSG.HardMathSupport.Dickson.I271.TabFi24
