module

public import Certificates.Data.CFSGNative.Chevalley.C2E6StdMatrix
public import CFSG.Monster.B.Classical.E6AdjointTable
public import CFSG.LieType.Chevalley.C2E6StdMatrixData
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.C2E6MinusSixDefs

@[expose] public section

namespace CFSG.LieType.Chevalley.C2E6Std.MatrixModel

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.Monster.B.Classical.E6Adjoint
open C2E6Std

@[expose] def nativeAB : Native.Mat × Native.Mat :=
  Native.genAB bracketCodes formBits fwdProg idxA idxB

end CFSG.LieType.Chevalley.C2E6Std.MatrixModel
