module

public import CFSG.Certificates.Kernel.Common.DeepRfl
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C00
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C01
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C02
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C03
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C04
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C05
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C06
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C07
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C08
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C09
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C10
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C11
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C12
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C13
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C14
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C15
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C16
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C17
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C18
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.KC.BSeed

open CFSG.KD.BSeed in
set_option maxHeartbeats 0 in
theorem bseed2_lit : CFSG.Blueprint.NativeSporadic.BSeed2 = String.ofList (charsOfS
    (M2C00.CH ++ M2C01.CH ++ M2C02.CH ++ M2C03.CH ++ M2C04.CH ++ M2C05.CH ++ M2C06.CH ++
      M2C07.CH ++ M2C08.CH ++ M2C09.CH ++ M2C10.CH ++ M2C11.CH ++ M2C12.CH ++ M2C13.CH ++
      M2C14.CH ++ M2C15.CH ++ M2C16.CH ++ M2C17.CH ++ M2C18.CH)) := by
  deep_rfl 60000000 98304

end CFSG.KC.BSeed

end
