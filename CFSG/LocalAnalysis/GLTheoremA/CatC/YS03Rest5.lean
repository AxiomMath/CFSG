module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03L33
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Asm

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys03Rest5


theorem ys03_of_kdata_rest5K
    (hL2 : KD1912TwoL2) (hL3 : KD1912TwoL3) (hU3 : KD1912TwoU3) (hR3 : KD1912TwoRows3)
    (hR5 : KD1912TwoRows5) (h264 : KD264Res) (h1426 : KD1426Cat) : YS03 :=
  ys03_of_kdata_rest3K hL2 hL3 hU3 hR3 hR5 kd1912TwoL33_holds
      (fun p hp hp2 => kd264K_of_res h264 p hp hp2) h1426

end Ys03Rest5

end CFSG.LocalAnalysis.GLTheoremA
