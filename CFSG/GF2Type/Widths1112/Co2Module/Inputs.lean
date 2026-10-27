module

public import CFSG.GF2Type.Widths1112.Co2Module.Idempotents
public import Certificates.Data.GF2W1112Co2U

public section

namespace CFSG.GF2Type.Widths1112.Co2Module

open CFSG.GF2W1112

@[expose] def uCode (v : F3Vec) : ℕ := (v 0).val + 3 * (v 1).val + 9 * (v 2).val + 27 * (v 3).val

@[expose] def uVec (c : ℕ) : F3Vec := fun i => ((c / 3 ^ i.val % 3 : ℕ) : ZMod 3)

@[expose] def uCls (w : F3Vec) : Fin 2 := if w12UClsTab.getD (uCode w) 0 == 1 then 1 else 0

@[expose] def uRoot (k : Fin 2) : F3Vec := uVec (w12URootCodes.getD k.val 0)

@[expose] def uPar (w : F3Vec) : F3Vec := uVec (w12UParTab.getD (uCode w) 0)

@[expose] def uGen (w : F3Vec) : Fin 2 := if w12UGenTab.getD (uCode w) 0 == 1 then 1 else 0

@[expose] def uC (w : F3Vec) : ZMod 3 := ((w12UCTab.getD (uCode w) 0 : ℕ) : ZMod 3)

@[expose] def uDepth (w : F3Vec) : ℕ := w12UDepthTab.getD (uCode w) 0

@[expose] def uA (k : ℕ) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.of fun i j => (((w12UConj.getD k #[]).getD (4 * i.val + j.val) 0 : ℕ) : ZMod 3)

@[expose] def uAInv (k : ℕ) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.of fun i j => (((w12UConjInv.getD k #[]).getD (4 * i.val + j.val) 0 : ℕ) : ZMod 3)

@[expose] def uW1 : F3Vec := uVec w12UW1Code

@[expose] def uV0 : F3Vec := uVec w12UV0Code

@[expose] def uW (i : Fin 10) : F3Vec := uVec (w12UOrbCodes.getD i.val 0)

@[expose] def uCr (i : Fin 10) : ZMod 3 := ((w12UCrTab.getD i.val 0 : ℕ) : ZMod 3)

@[expose] def uCt : ZMod 3 := ((w12UCtVal : ℕ) : ZMod 3)

@[expose] def uSigma (k : Fin 8) (i : Fin 10) : Fin 10 :=
  ⟨w12UDecSigma.getD (k.val * 10 + i.val) 0 % 10, Nat.mod_lt _ (by norm_num)⟩

@[expose] def uU (k : Fin 8) (i : Fin 10) (j : Fin 2) : F3Vec :=
  uVec (w12UDecU.getD (k.val * 20 + i.val * 2 + j.val) 0)

@[expose] def uEps (k : Fin 8) (i : Fin 10) (j : Fin 2) : ℕ :=
  w12UDecEps.getD (k.val * 20 + i.val * 2 + j.val) 0

@[expose] def uTw (j : Fin 8) : List (Fin 2 × ℕ) :=
  (w12UTauWords.getD j.val []).map fun q => (⟨q.1 % 2, Nat.mod_lt _ (by norm_num)⟩, q.2)

@[expose] def uKk (j : Fin 8) : ℕ := w12UTauOrd.getD j.val 0

end CFSG.GF2Type.Widths1112.Co2Module
