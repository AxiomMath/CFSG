module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD.CycAbstract
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD.FlagStab

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD

open CFSG.LieType.Universal.Spin Matrix

@[expose] def lrM (n : ℕ) (i j : Fin n) (s t : Bool) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  Matrix.of fun a b => (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) a b +
    (if a = flagIdx i s ∧ b = flagIdx j (!t) then 1 else 0) -
    (if a = flagIdx j t ∧ b = flagIdx i (!s) then 1 else 0)

@[expose] def posM (n : ℕ) (k : Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  lrM n (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k)

@[expose] def negM (n : ℕ) (k : Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  lrM n (rootIdxD' n k) (rootIdxD n k) (!rootSignD n k) false

theorem leviMat_four : LeviIdentities (posM 4 1) (negM 4 1) (posM 4 2) (negM 4 2) (posM 4 3)
    (negM 4 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide +kernel

theorem leviMat_five : LeviIdentities (posM 5 2) (negM 5 2) (posM 5 3) (negM 5 3) (posM 5 4)
    (negM 5 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide +kernel

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD
