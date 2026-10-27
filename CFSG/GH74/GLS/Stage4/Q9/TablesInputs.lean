module

public import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public import CFSG.CharacterTheory.PSL2Table
public meta import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public meta import CFSG.CharacterTheory.PSL2Table.Basic
public meta import Mathlib
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.Open.Defs
public meta import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Orthogonality

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open CFSG CFSG.PSL2Table
open scoped MatrixGroups
local notation "𝕄" => Matrix (Fin 2) (Fin 2) F9

namespace Tables

@[expose] def aEight : F9ˣ := Units.mk0 nu nu_ne_zero

@[expose] def aFour : F9ˣ := aEight * aEight

@[expose] def R3 : SL2 := diag aFour

@[expose] def R4 : SL2 := diag aEight

@[expose] def Y : SL2 := nsElem nu ⟨2, 1⟩ ⟨1, 2⟩ (by decide)

@[expose] def Y2 : SL2 := Y * Y

end Tables

open Tables
@[expose] def repList : Fin 7 → SL2 := ![1, unip 1, unip nu, R3, R4, Y, Y2]

namespace Tables

@[expose] def IsRepOf (R X : SL2) : Prop := X = R ∨ X = R * minusOne

end Tables

namespace Tables

@[expose] def allF9 : List F9 :=
  (List.range 3).flatMap fun a => (List.range 3).map fun b => (⟨(a : ZMod 3), (b : ZMod 3)⟩ : F9)

end Tables

open Tables
@[expose] def allSL2 : List SL2 :=
  allF9.flatMap fun a => allF9.flatMap fun b => allF9.flatMap fun c => allF9.filterMap fun d =>
    if h : a * d - b * c = 1 then
      some (⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩ : SL2) else none

namespace Tables

@[expose] def invSL (c : SL2) : SL2 :=
  ⟨!![(c : 𝕄) 1 1, -(c : 𝕄) 0 1; -(c : 𝕄) 1 0, (c : 𝕄) 0 0], by
    have h := c.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

@[expose] def conjSL (c M : SL2) : SL2 :=
  let p := (c : 𝕄) 0 0
  let q := (c : 𝕄) 0 1
  let r := (c : 𝕄) 1 0
  let s := (c : 𝕄) 1 1
  let a := (M : 𝕄) 0 0
  let b := (M : 𝕄) 0 1
  let e := (M : 𝕄) 1 0
  let d := (M : 𝕄) 1 1
  let x00 := p * a + q * e
  let x01 := p * b + q * d
  let x10 := r * a + s * e
  let x11 := r * b + s * d
  ⟨!![x00 * s - x01 * r, x01 * p - x00 * q; x10 * s - x11 * r, x11 * p - x10 * q], by
    have hc := c.det_coe
    have hM := M.det_coe
    rw [Matrix.det_fin_two] at hc hM
    rw [Matrix.det_fin_two_of]
    simp only [x00, x01, x10, x11, p, q, r, s, a, b, e, d]
    linear_combination ((c : 𝕄) 0 0 * (c : 𝕄) 1 1 - (c : 𝕄) 0 1 * (c : 𝕄) 1 0) ^ 2 * hM +
      (((c : 𝕄) 0 0 * (c : 𝕄) 1 1 - (c : 𝕄) 0 1 * (c : 𝕄) 1 0) + 1) * hc⟩

end Tables

@[expose] def trSL2 (M : SL2) : F9 := (M : 𝕄) 0 0 + (M : 𝕄) 1 1

@[expose] def repIdx (M : SL2) : Fin 7 :=
  if trSL2 M * trSL2 M = 4 then
    if (M : 𝕄) 0 1 = 0 ∧ (M : 𝕄) 1 0 = 0 then 0
    else if IsSquare (if (M : 𝕄) 0 1 ≠ 0 then (M : 𝕄) 0 1 else (M : 𝕄) 1 0) then 1 else 2
  else if trSL2 M = 0 then 3
  else if trSL2 M * trSL2 M = -1 then 4
  else if trSL2 M * trSL2 M = ⟨0, 1⟩ then 5 else 6

@[expose] def classSwap : Fin 7 → Fin 7 := ![0, 2, 1, 3, 4, 5, 6]



open Tables

open Tables

open Tables


open Tables

open Tables

open Tables

open Tables
@[expose] def orderFn (j : Fin 7) (t : F9) : ℕ :=
  if j = 0 then (if t = 2 then 1 else 2)
  else if j = 1 ∨ j = 2 then (if t = 2 then 3 else 6)
  else if j = 3 then 4
  else if j = 4 then 8
  else if j = 5 then (if t = ⟨1, 2⟩ then 5 else 10)
  else (if t = ⟨1, 1⟩ then 5 else 10)


open Tables
end CFSG.GH74.GLS.Stage4.Q9
