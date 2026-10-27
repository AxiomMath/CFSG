module

public import CFSG.Certificates.Kernel.Common.DeepRfl
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C00
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C01
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C02
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C03
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C04
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C05
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C06
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C07
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C08
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C09
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C10
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C11
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C12
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C13
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C14
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C15
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C16
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C17
public import CFSG.Certificates.Kernel.BSeed.Chunks.M1C18
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.KC.BSeed

open CFSG.KD.BSeed in
set_option maxHeartbeats 0 in
theorem bseed1_lit : CFSG.Blueprint.NativeSporadic.BSeed1 = String.ofList (charsOfS
    (M1C00.CH ++ M1C01.CH ++ M1C02.CH ++ M1C03.CH ++ M1C04.CH ++ M1C05.CH ++ M1C06.CH ++
      M1C07.CH ++ M1C08.CH ++ M1C09.CH ++ M1C10.CH ++ M1C11.CH ++ M1C12.CH ++ M1C13.CH ++
      M1C14.CH ++ M1C15.CH ++ M1C16.CH ++ M1C17.CH ++ M1C18.CH)) := by
  deep_rfl 60000000 98304

end CFSG.KC.BSeed

end
