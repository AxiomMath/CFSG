module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CosetNative
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2CheckInputs
public import Certificates.Certificate4050
public meta import Std.Data.HashMap

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm

theorem j2_treeValid : treeValid 4725 j2Data.par j2Data.gen :=
  Certificates.certificate4050.1

theorem j2_invValid :
    invValid 315 j2Data.ta j2Data.tb j2Data.tai j2Data.tbi :=
  Certificates.certificate4050.2.1

theorem j2_slpValid : slpValidAux j2Data.prog 2 = true :=
  Certificates.certificate4050.2.2.1

theorem j2_enumOK :
    BaseEnumOK 315 (List.range 315) j2RG j2RGi j2Enum.1 j2Enum.2.1 j2Enum.2.2 :=
  Certificates.certificate4050.2.2.2.1

theorem j2_enum_size : j2Enum.1.size = 128 :=
  Certificates.certificate4050.2.2.2.2.1

theorem j2_edgeOK :
    edgeOK 315 4725 (ptsOf (List.range 315) j2RG) j2Enum.1 j2Keys j2Data.ta
    j2Data.tb j2Data.Aa j2Data.Ab j2T j2U = true :=
  Certificates.certificate4050.2.2.2.2.2.1

theorem j2_blocksClosed :
    blocksClosed j2ROm 4725 j2Data.Aa j2Data.Ab j2Data.par j2Data.gen
    j2Data.xs j2Blocks :=
  Certificates.certificate4050.2.2.2.2.2.2.1

theorem j2_repsOK : repsOK j2ROm 4725 j2Data.repR j2Reps j2Orbs :=
  Certificates.certificate4050.2.2.2.2.2.2.2.1

theorem j2_closureOK :
    closureOK j2ROm 4725 j2Data.Aa j2Data.Ab j2Data.par j2Data.gen j2Data.xs
    j2Blocks j2Reps :=
  Certificates.certificate4050.2.2.2.2.2.2.2.2.1

theorem j2_shapeOK : shapeOK 4725 j2Blocks :=
  Certificates.certificate4050.2.2.2.2.2.2.2.2.2.1

theorem j2_xsOK : xsOK 4725 j2Data.xs :=
  Certificates.certificate4050.2.2.2.2.2.2.2.2.2.2.1

theorem j2_qpOK : qpOK 315 j2NT j2Data.qp :=
  Certificates.certificate4050.2.2.2.2.2.2.2.2.2.2.2.1

theorem j2_aszOK : aszOK 4725 j2Data.Aa j2Data.Ab :=
  Certificates.certificate4050.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.QuasithinUnique.Setup.X1
