module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeSylow
public import CFSG.Sporadic.J2.Simple
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeJ2Tab

public noncomputable section

set_option maxHeartbeats 4000000

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree

open CFSG.Sporadic.J2 CFSG.Blueprint
open CFSG.Sporadic.J1 (toM toM_mulL toM_idL toM_powL wfM_mulL wfM_idL wfM_iff getD_of_wfM)
open CFSG.Sporadic.J1.Native (wfM mulL idL powL)

@[expose] def letJ2 (l : ℕ) : J := if l = 1 then a else b

@[expose] def wordJ2 (w : List ℕ) : J := (w.map letJ2).prod

@[expose] def letL (l : ℕ) : List (List ℕ) := if l = 1 then Native.mA else Native.mB

@[expose] def wordL : List ℕ → List (List ℕ)
  | [] => idL 14
  | l :: w => mulL 5 14 (letL l) (wordL w)

@[expose] def LRep (L : List (List ℕ)) (g : J) : Prop :=
  wfM 14 L = true ∧ mat g = toM 5 14 L

theorem LRep.mul {L M : List (List ℕ)} {g h : J} (hg : LRep L g) (hh : LRep M h) :
    LRep (mulL 5 14 L M) (g * h) :=
  ⟨wfM_mulL hg.1, by rw [mat_mul, hg.2, hh.2, toM_mulL hg.1 hh.1]⟩

theorem LRep.one : LRep (idL 14) 1 := ⟨wfM_idL 14, by rw [mat_one, toM_idL]⟩

theorem LRep.pow {L : List (List ℕ)} {g : J} (hg : LRep L g) (e : ℕ) :
    LRep (powL 5 14 L e) (g ^ e) :=
  ⟨by induction e with
      | zero => exact wfM_idL 14
      | succ e _ => exact wfM_mulL hg.1,
    by rw [mat_pow, hg.2, toM_powL hg.1]⟩

theorem LRep.eq {L : List (List ℕ)} {g h : J} (hg : LRep L g) (hh : LRep L h) : g = h :=
  mat_injective (hg.2.trans hh.2.symm)

theorem letRep (l : ℕ) : LRep (letL l) (letJ2 l) := by
  unfold letL letJ2
  split_ifs
  · exact ⟨by decide, mat_a⟩
  · exact ⟨by decide, mat_b⟩

theorem wordRep (w : List ℕ) : LRep (wordL w) (wordJ2 w) := by
  induction w with
  | nil => exact LRep.one
  | cons l w ih => exact (letRep l).mul ih

theorem toM_inj {X Y : List (List ℕ)} (hX : wfM 14 X = true) (hY : wfM 14 Y = true)
    (hXp : ∀ r ∈ X, ∀ e ∈ r, e < 5) (hYp : ∀ r ∈ Y, ∀ e ∈ r, e < 5)
    (h : toM 5 14 X = toM 5 14 Y) : X = Y := by
  have hXl : X.length = 14 := (wfM_iff.mp hX).1
  have hYl : Y.length = 14 := (wfM_iff.mp hY).1
  refine List.ext_getElem (hXl.trans hYl.symm) fun i hi hi' => ?_
  have hi14 : i < 14 := hXl ▸ hi
  have hXr := getD_of_wfM hX i hi14
  have hYr := getD_of_wfM hY i hi14
  have hXi : X.getD i [] = X[i] := List.getD_eq_getElem _ _ hi
  have hYi : Y.getD i [] = Y[i] := List.getD_eq_getElem _ _ hi'
  rw [hXi] at hXr
  rw [hYi] at hYr
  refine List.ext_getElem (hXr.trans hYr.symm) fun j hj hj' => ?_
  have hj14 : j < 14 := hXr ▸ hj
  have := congrFun (congrFun h ⟨i, hi14⟩) ⟨j, hj14⟩
  simp only [toM, Matrix.of_apply, hXi, hYi, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at this
  have h1 := hXp _ (List.getElem_mem hi) _ (List.getElem_mem hj)
  have h2 := hYp _ (List.getElem_mem hi') _ (List.getElem_mem hj')
  have := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 this
  rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this

@[expose] def j2xw : List ℕ :=
  [1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2,
    1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1]

@[expose] def j2yw : List ℕ :=
  [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2,
    2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2,
    1, 2, 1]

@[expose] def j2x : J := wordJ2 j2xw
@[expose] def j2y : J := wordJ2 j2yw
@[expose] def j2z : J := j2x * j2y * (j2x * j2x) * (j2y * j2y)

@[expose] def j2f (p : Fin 3 × Fin 3 × Fin 3) : J :=
  j2x ^ (p.1 : ℕ) * j2y ^ (p.2.1 : ℕ) * j2z ^ (p.2.2 : ℕ)

@[expose] def xL : List (List ℕ) :=
  [[0, 2, 4, 4, 1, 2, 0, 2, 3, 2, 1, 0, 4, 4],
    [0, 1, 2, 4, 4, 0, 1, 2, 1, 0, 0, 4, 0, 2],
    [2, 2, 4, 2, 2, 1, 0, 1, 2, 3, 3, 3, 4, 0],
    [1, 1, 3, 2, 0, 2, 1, 4, 3, 4, 4, 4, 1, 1],
    [2, 2, 3, 2, 4, 4, 0, 1, 3, 3, 4, 0, 3, 1],
    [3, 2, 1, 4, 1, 2, 0, 4, 1, 1, 3, 2, 0, 2],
    [0, 0, 2, 2, 3, 0, 1, 3, 4, 0, 1, 1, 4, 1],
    [2, 0, 0, 0, 2, 3, 0, 1, 3, 1, 0, 2, 1, 0],
    [2, 1, 4, 0, 1, 2, 3, 4, 2, 0, 4, 2, 2, 1],
    [3, 4, 2, 1, 4, 4, 0, 2, 0, 1, 4, 2, 0, 2],
    [3, 1, 0, 0, 3, 0, 0, 3, 3, 2, 2, 4, 4, 3],
    [1, 2, 4, 1, 0, 4, 2, 2, 0, 4, 3, 3, 0, 3],
    [0, 4, 3, 2, 4, 3, 3, 2, 3, 0, 4, 4, 0, 0],
    [1, 0, 0, 0, 2, 0, 0, 2, 2, 0, 2, 1, 2, 1]]

@[expose] def yL : List (List ℕ) :=
  [[3, 3, 0, 2, 3, 1, 1, 2, 0, 2, 2, 4, 1, 4],
    [2, 0, 2, 3, 3, 0, 3, 0, 0, 3, 0, 3, 4, 0],
    [2, 0, 4, 4, 3, 4, 3, 3, 0, 0, 1, 4, 3, 4],
    [4, 3, 3, 1, 4, 0, 1, 0, 2, 2, 4, 4, 3, 0],
    [4, 1, 1, 1, 0, 4, 2, 2, 2, 1, 1, 1, 4, 2],
    [1, 0, 2, 4, 2, 4, 3, 1, 4, 0, 0, 2, 0, 1],
    [3, 0, 1, 0, 1, 1, 3, 1, 1, 1, 3, 2, 3, 0],
    [2, 4, 0, 4, 0, 4, 3, 1, 0, 4, 3, 1, 3, 1],
    [0, 4, 1, 2, 3, 0, 4, 1, 0, 0, 0, 2, 3, 2],
    [3, 1, 4, 4, 4, 4, 2, 2, 3, 1, 0, 1, 1, 3],
    [3, 1, 2, 4, 3, 2, 1, 4, 0, 4, 2, 2, 4, 3],
    [0, 4, 0, 0, 1, 2, 1, 4, 0, 2, 1, 2, 4, 2],
    [3, 4, 0, 4, 2, 3, 4, 3, 0, 1, 4, 4, 1, 2],
    [3, 1, 0, 4, 1, 4, 2, 1, 3, 4, 3, 0, 0, 2]]

theorem xL_eq : wordL j2xw = xL := by decide +kernel
theorem yL_eq : wordL j2yw = yL := by decide +kernel

@[expose] def zL : List (List ℕ) :=
  [[4, 2, 4, 0, 3, 3, 1, 4, 4, 3, 2, 4, 1, 1],
    [2, 2, 2, 3, 1, 0, 2, 4, 4, 0, 2, 4, 2, 2],
    [0, 2, 0, 4, 4, 1, 1, 4, 2, 4, 3, 1, 2, 4],
    [1, 4, 0, 2, 3, 3, 4, 1, 4, 4, 2, 0, 1, 4],
    [2, 3, 4, 1, 0, 1, 0, 4, 1, 1, 3, 3, 4, 2],
    [1, 0, 2, 3, 4, 2, 2, 0, 3, 0, 2, 3, 4, 4],
    [1, 0, 3, 4, 0, 0, 4, 2, 1, 4, 3, 0, 1, 0],
    [3, 2, 4, 3, 2, 3, 0, 1, 1, 1, 2, 0, 4, 0],
    [3, 0, 1, 0, 4, 1, 0, 3, 3, 1, 0, 1, 4, 2],
    [3, 3, 3, 4, 1, 1, 0, 3, 3, 2, 1, 1, 4, 4],
    [1, 1, 2, 3, 1, 0, 1, 1, 0, 4, 2, 2, 4, 0],
    [4, 3, 2, 1, 2, 2, 4, 4, 2, 4, 3, 3, 2, 0],
    [4, 1, 2, 4, 2, 1, 4, 4, 4, 3, 2, 0, 2, 3],
    [1, 1, 3, 4, 1, 0, 4, 3, 3, 4, 4, 4, 1, 3]]

theorem zL_eq : mulL 5 14 (mulL 5 14 (mulL 5 14 xL yL) (mulL 5 14 xL xL)) (mulL 5 14 yL yL) = zL := by
  decide +kernel

@[expose] def fL (p : Fin 3 × Fin 3 × Fin 3) : List (List ℕ) :=
  mulL 5 14 (mulL 5 14 (powL 5 14 xL p.1) (powL 5 14 yL p.2.1)) (powL 5 14 zL p.2.2)

theorem xRep : LRep xL j2x := xL_eq ▸ wordRep j2xw
theorem yRep : LRep yL j2y := yL_eq ▸ wordRep j2yw
theorem zRep : LRep zL j2z :=
  zL_eq ▸ (((xRep.mul yRep).mul (xRep.mul xRep)).mul (yRep.mul yRep))
theorem fRep (p : Fin 3 × Fin 3 × Fin 3) : LRep (fL p) (j2f p) :=
  ((xRep.pow _).mul (yRep.pow _)).mul (zRep.pow _)

@[expose] def j2tws : List (List ℕ) :=
  [[],
    [2, 1, 2, 2, 1, 2, 1, 2, 2],
    [2, 1, 2, 2, 1, 2, 1, 2, 2],
    [2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2],
    [1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1],
    [2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2],
    [2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2],
    [2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2],
    [1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1],
    [2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2,
      1, 2, 2, 1, 2],
    [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
      1],
    [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2],
    [2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2],
    [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2],
    [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1],
    [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2,
      1, 2, 2, 1, 2, 2, 1, 2, 1, 2],
    [2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2,
      1, 2, 2, 1, 2, 1, 2, 1, 2, 2],
    [1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2,
      1, 2, 2, 1, 2, 1],
    [2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2,
      1, 2, 2, 1, 2],
    [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2],
    [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
      1],
    [2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2,
      1, 2, 2, 1, 2, 1, 2, 1, 2, 2],
    [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2,
      1, 2, 2, 1, 2, 2, 1, 2, 1, 2],
    [1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2,
      1, 2, 2, 1, 2, 1],
    [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1],
    [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2],
    [2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2]]

@[expose] def j2tw (p : Fin 3 × Fin 3 × Fin 3) : List ℕ :=
  j2tws.getD (9 * (p.1 : ℕ) + 3 * (p.2.1 : ℕ) + (p.2.2 : ℕ)) []

@[expose] def j2σx (p : Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 :=
  (p.1 + 1, p.2.1, p.2.2 - p.2.1)

@[expose] def j2σy (p : Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 :=
  (p.1, p.2.1 + 1, p.2.2)

theorem j2_gen_facts : j2x ^ 3 = 1 ∧ j2y ^ 3 = 1 := by
  have h1 : powL 5 14 xL 3 = idL 14 := by decide +kernel
  have h2 : powL 5 14 yL 3 = idL 14 := by decide +kernel
  exact ⟨(xRep.pow 3).eq (h1 ▸ LRep.one), (yRep.pow 3).eq (h2 ▸ LRep.one)⟩

theorem j2f_σx : ∀ p, j2f p * j2x = j2f (j2σx p) := by
  have hF := J2Tab.ft_rep LRep LRep.mul LRep.one j2x j2y j2z xL yL zL xRep yRep zRep
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hxc : CFSG.Sporadic.J1.Native.colsL 14 xL = J2Tab.xC := by decide +kernel
  intro p
  have h : mulL 5 14 (J2Tab.FT p) xL = J2Tab.FT (j2σx p) := J2Tab.sx_chk xL hxc p
  exact ((hF p).mul xRep).eq (h ▸ hF (j2σx p))

theorem j2f_σy : ∀ p, j2f p * j2y = j2f (j2σy p) := by
  have hF := J2Tab.ft_rep LRep LRep.mul LRep.one j2x j2y j2z xL yL zL xRep yRep zRep
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hyc : CFSG.Sporadic.J1.Native.colsL 14 yL = J2Tab.yC := by decide +kernel
  intro p
  have h : mulL 5 14 (J2Tab.FT p) yL = J2Tab.FT (j2σy p) := J2Tab.sy_chk yL hyc p
  exact ((hF p).mul yRep).eq (h ▸ hF (j2σy p))

theorem j2f_one : ∃ p, j2f p = 1 := by
  have h : fL (0, 0, 0) = idL 14 := by decide +kernel
  exact ⟨(0, 0, 0), (fRep _).eq (h ▸ LRep.one)⟩

theorem j2f_tinv : ∀ p, ∃ t, t * j2f p * t⁻¹ = (j2f p)⁻¹ := by
  have hF := J2Tab.ft_rep LRep LRep.mul LRep.one j2x j2y j2z xL yL zL xRep yRep zRep
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro p
  obtain ⟨t, hW⟩ : ∃ t, LRep (J2Tab.T p) t :=
    ⟨_, J2Tab.t_rep LRep LRep.mul LRep.one j2x j2y j2z xL yL zL xRep yRep zRep
      (by decide +kernel) (by decide +kernel) (by decide +kernel) letJ2 letRep p⟩
  refine ⟨t, ?_⟩
  have e1 : t * j2f p = (j2f p * j2f p) * t :=
    (hW.mul (hF p)).eq (J2Tab.tinv_chk p ▸ (((hF p).mul (hF p)).mul hW))
  have e2 : j2f p * j2f p * j2f p = 1 :=
    (((hF p).mul (hF p)).mul (hF p)).eq (J2Tab.h3_chk p ▸ LRep.one)
  calc t * j2f p * t⁻¹
      = (j2f p * j2f p * t) * t⁻¹ := by rw [e1]
    _ = j2f p * j2f p := by group
    _ = (j2f p)⁻¹ := eq_inv_of_mul_eq_one_left e2

theorem j2f_inj : Function.Injective j2f := by
  have hF := J2Tab.ft_rep LRep LRep.mul LRep.one j2x j2y j2z xL yL zL xRep yRep zRep
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro p q h
  apply J2Tab.ft_inj
  exact toM_inj (hF p).1 (hF q).1 (J2Tab.ft_lt p) (J2Tab.ft_lt q)
    (((hF p).2.symm.trans (congrArg mat h)).trans (hF q).2)

theorem j2f_mem : ∀ p, j2f p ∈ Subgroup.closure ({j2x, j2y} : Set J) := by
  intro p
  have hx : j2x ∈ Subgroup.closure ({j2x, j2y} : Set J) := Subgroup.subset_closure (by simp)
  have hy : j2y ∈ Subgroup.closure ({j2x, j2y} : Set J) := Subgroup.subset_closure (by simp)
  have hz : j2z ∈ Subgroup.closure ({j2x, j2y} : Set J) :=
    mul_mem (mul_mem (mul_mem hx hy) (mul_mem hx hx)) (mul_mem hy hy)
  exact mul_mem (mul_mem (pow_mem hx _) (pow_mem hy _)) (pow_mem hz _)

theorem real3_j2 : Real3 J := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  choose t ht using j2f_tinv
  exact real3_of_gen j2_gen_facts.1 j2_gen_facts.2 j2f j2σx j2σy j2f_inj j2f_mem
    j2f_one j2f_σx j2f_σy 3 (by simp) (by rw [card_J]; norm_num)
    fun p => ⟨t p, ht p⟩

theorem real3_of_j2 {X : Type} [Group X]
    (e : X ≃* NativeSporadic.Carrier .J2) : Real3 X :=
  Real3.of_mulEquiv (e.trans nativeEquiv) real3_j2

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree
