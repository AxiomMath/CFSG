module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25SA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X4

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


theorem centExt_of_leaves (hQ : P25X_QTF) (hSqL : P25X_SqZL) (hF : P25X_NoFace) : P25_CentExt :=
  centExt_of_parts (centExtMix_of hQ hSqL) (centExtNoMix_of hQ (noMixParity_of_leaves hQ hF))

theorem a4_of_leaves (hQ : P25X_QTF) (hSqL : P25X_SqZL) (hF : P25X_NoFace) : P25_A4 :=
  a4_of_centExt (centExt_of_leaves hQ hSqL hF)

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
