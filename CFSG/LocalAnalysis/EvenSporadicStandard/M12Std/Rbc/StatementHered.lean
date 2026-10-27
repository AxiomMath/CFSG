module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.ChildrenHered
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierCoreBranches
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenResidual
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.KDNP
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Rows
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

@[expose] def FS79RbcHered : Prop :=
  KDNP →
  CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels →
  CFSG.ComponentClassification.UFrontier.GH74ModelsInput →
  CFSG.EvenSporadicStandard.Induction.CTEvenResidualStatement →
  CFSG.EvenSporadicStandard.Induction.ChildL34WHered →
  CFSG.EvenSporadicStandard.Induction.ChildHeWHered →
  RowsToChild3

end CFSG.EvenSporadicStandard.M12Std.Rbc
