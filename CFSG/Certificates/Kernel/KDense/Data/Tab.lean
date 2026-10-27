module

public import CFSG.Certificates.Kernel.KDense.Data.Tab0
public import CFSG.Certificates.Kernel.KDense.Data.Tab1
public import CFSG.Certificates.Kernel.KDense.Data.Tab2
public import CFSG.Certificates.Kernel.KDense.Data.Tab3
public import CFSG.Certificates.Kernel.KDense.Data.Tab4
public import CFSG.Certificates.Kernel.KDense.Data.Tab5
public import CFSG.Certificates.Kernel.KDense.Data.Tab6
public import CFSG.Certificates.Kernel.KDense.Data.Tab7
public import CFSG.Certificates.Kernel.KDense.Data.Tab8
public import CFSG.Certificates.Kernel.KDense.Data.Fix

public section

#kc_select CFSG.KD.KDT netXf netX 72
#kc_select CFSG.KD.KDT sgnXf sgnX 72
#kc_select CFSG.KD.KDT netWf netW 72
#kc_select CFSG.KD.KDT sgnWf sgnW 72
#kc_select CFSG.KD.KDT netAf netA 72

namespace CFSG.KD.KDT

open CFSG.KC.KDense

@[expose] noncomputable def T : Tab := ⟨[arr0, arr1, arr2, arr3, arr4, arr5, arr6, arr7, arr8, arr9, arr10, arr11, arr12, arr13, arr14, arr15, arr16, arr17, arr18, arr19, arr20, arr21, arr22, arr23, arr24, arr25, arr26, arr27, arr28, arr29, arr30, arr31, arr32, arr33, arr34, arr35, arr36, arr37, arr38, arr39, arr40, arr41, arr42, arr43, arr44, arr45, arr46, arr47, arr48, arr49, arr50, arr51, arr52, arr53, arr54, arr55, arr56, arr57, arr58, arr59, arr60, arr61, arr62, arr63, arr64, arr65, arr66, arr67, arr68, arr69, arr70, arr71], netXf, sgnXf, netWf, sgnWf, netAf⟩

end CFSG.KD.KDT

end
