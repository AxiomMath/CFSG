module

public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open CFSG.PSL3Four.Native

@[expose] def m12AT : Tab := #[3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5]

@[expose] def m12BT : Tab := #[7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]

@[expose] def m12Gens : Array Tab := #[m12AT, m12BT]

@[expose] def m12a₀T : Tab := #[10, 5, 8, 4, 3, 1, 9, 11, 2, 6, 0, 7]

@[expose] def m12b₀T : Tab := m12AT

@[expose] def hfiMem (T : Array Tab) (x : Tab) : Bool := anyBelow T.size fun k => T[k]! == x

@[expose] def hfiM12Check (EM OA OB : Enum) : Bool :=
  let ginv := m12Gens.map (invTab 12)
  let C := centTabs 12 EM.tabs m12a₀T
  enumOK 12 m12Gens EM && EM.tabs.size == 95040 &&
    orbitOK 12 m12Gens ginv m12a₀T OA && OA.tabs.size == 396 &&
    orbitOK 12 m12Gens ginv m12b₀T OB && OB.tabs.size == 495 &&
    hfiMem EM.tabs m12a₀T && hfiMem EM.tabs m12b₀T &&
    comp 12 m12a₀T m12a₀T == idTab 12 && !(m12a₀T == idTab 12) &&
    comp 12 m12b₀T m12b₀T == idTab 12 && !(m12b₀T == idTab 12) &&
    coverOK 12 EM.tabs #[OA.tabs, OB.tabs] &&
    (allBelow C.size fun k =>
      !(comp 12 C[k]! C[k]! == idTab 12 && !(C[k]! == idTab 12) && !(C[k]! == m12a₀T) &&
          hfiMem OA.tabs C[k]! && hfiMem OA.tabs (comp 12 m12a₀T C[k]!)) ||
        anyBelow EM.tabs.size fun j =>
          comp 12 EM.tabs[j]! m12a₀T == comp 12 C[k]! EM.tabs[j]! &&
            comp 12 EM.tabs[j]! C[k]! == comp 12 (comp 12 m12a₀T C[k]!) EM.tabs[j]!)

end CFSG.EvenSporadicStandard.HSStd.HFI
