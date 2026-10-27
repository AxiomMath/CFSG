module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeSylowDefs

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

open CFSG.EvenSmallLie.OmegaEight (matMulM idCode)

@[expose] def commP (i k : ℕ) : Bool :=
  matMulM (OmegaEight.saMat i) (OmegaEight.saMat k) == matMulM (OmegaEight.saMat k) (OmegaEight.saMat i)

@[expose] def conjP (c a w : ℕ) : Bool :=
  matMulM (OmegaEight.saMat c) (OmegaEight.saMat a) == matMulM (OmegaEight.saMat w) (OmegaEight.saMat c)

@[expose] def invP (i : ℕ) : Bool :=
  i != 0 && matMulM (OmegaEight.saMat i) (OmegaEight.saMat i) == idCode

end CFSG.EvenSmallLie.OmegaEight.SplitC

namespace CFSG.EvenSmallLie.OmegaEightMinus

open CFSG.EvenSmallLie.OmegaEight (matMulM idCode)

@[expose] def commM (i k : ℕ) : Bool :=
  matMulM (saMat i) (saMat k) == matMulM (saMat k) (saMat i)

@[expose] def conjM (c a w : ℕ) : Bool :=
  matMulM (saMat c) (saMat a) == matMulM (saMat w) (saMat c)

@[expose] def invM (i : ℕ) : Bool :=
  i != 0 && matMulM (saMat i) (saMat i) == idCode

end CFSG.EvenSmallLie.OmegaEightMinus

end
