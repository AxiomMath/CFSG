module

public import Certificates.Data.CFSGNative.GammaU.Pairs
public import CFSG.GF2Type.Smith1979.GammaU.NativeBridge

public section

namespace CFSG.GF2Type.Smith1979.GammaU

open StepA

theorem native_invR : @CFSG.GammaU.Native.invR = @Viol.invR := rfl

theorem native_okRows : @CFSG.GammaU.Native.okRows = @Viol.okRows := rfl

theorem native_enumGrp : @CFSG.GammaU.Native.enumGrp = @Enum.enumGrp := by
  funext gs
  unfold CFSG.GammaU.Native.enumGrp Enum.enumGrp
  rw [native_bfsClosure]
  rfl

theorem native_n2Gens : @CFSG.GammaU.Native.n2Gens = @ResPair.n2Gens := rfl

theorem native_resConj : @CFSG.GammaU.Native.resConj = @ResPair.resConj := rfl

end CFSG.GF2Type.Smith1979.GammaU
