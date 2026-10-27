module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.A2
open CFSG.PSL3Four CFSG.PSL3Four.Native

set_option compiler.extract_closed false

@[expose] def uTabs : Array Tab :=
  #[
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41],
    #[0, 1, 2, 3, 4, 6, 5, 8, 7, 10, 9, 12, 11, 14, 13, 16, 15, 18, 17, 20, 19, 27, 22, 31, 39, 35, 26, 21, 29, 28, 30, 23, 37, 40, 34, 25, 41, 32, 38, 24, 33, 36],
    #[0, 1, 2, 3, 4, 7, 8, 5, 6, 11, 12, 9, 10, 15, 16, 13, 14, 19, 20, 17, 18, 29, 22, 41, 37, 33, 26, 28, 27, 21, 30, 36, 39, 25, 34, 40, 31, 24, 38, 32, 35, 23],
    #[0, 1, 2, 3, 4, 8, 7, 6, 5, 12, 11, 10, 9, 16, 15, 14, 13, 20, 19, 18, 17, 28, 22, 36, 32, 40, 26, 29, 21, 27, 30, 41, 24, 35, 34, 33, 23, 39, 38, 37, 25, 31],
    #[0, 2, 1, 4, 3, 5, 6, 7, 8, 10, 9, 12, 11, 15, 16, 13, 14, 20, 19, 18, 17, 23, 22, 21, 25, 24, 26, 31, 36, 41, 30, 27, 40, 37, 34, 39, 28, 33, 38, 35, 32, 29],
    #[0, 2, 1, 4, 3, 6, 5, 8, 7, 9, 10, 11, 12, 16, 15, 14, 13, 19, 20, 17, 18, 31, 22, 27, 35, 39, 26, 23, 41, 36, 30, 21, 33, 32, 34, 24, 29, 40, 38, 25, 37, 28],
    #[0, 2, 1, 4, 3, 7, 8, 5, 6, 12, 11, 10, 9, 13, 14, 15, 16, 18, 17, 20, 19, 41, 22, 29, 33, 37, 26, 36, 31, 23, 30, 28, 35, 24, 34, 32, 27, 25, 38, 40, 39, 21],
    #[0, 2, 1, 4, 3, 8, 7, 6, 5, 11, 12, 9, 10, 14, 13, 16, 15, 17, 18, 19, 20, 36, 22, 28, 40, 32, 26, 41, 23, 31, 30, 29, 25, 39, 34, 37, 21, 35, 38, 33, 24, 27],
    #[0, 3, 4, 1, 2, 5, 6, 7, 8, 11, 12, 9, 10, 16, 15, 14, 13, 18, 17, 20, 19, 25, 22, 24, 23, 21, 26, 35, 40, 33, 30, 39, 36, 29, 34, 27, 32, 41, 38, 31, 28, 37],
    #[0, 3, 4, 1, 2, 6, 5, 8, 7, 12, 11, 10, 9, 15, 16, 13, 14, 17, 18, 19, 20, 35, 22, 39, 31, 27, 26, 25, 33, 40, 30, 24, 41, 28, 34, 21, 37, 36, 38, 23, 29, 32],
    #[0, 3, 4, 1, 2, 7, 8, 5, 6, 9, 10, 11, 12, 14, 13, 16, 15, 20, 19, 18, 17, 33, 22, 37, 41, 29, 26, 40, 35, 25, 30, 32, 31, 21, 34, 28, 39, 23, 38, 36, 27, 24],
    #[0, 3, 4, 1, 2, 8, 7, 6, 5, 10, 9, 12, 11, 13, 14, 15, 16, 19, 20, 17, 18, 40, 22, 32, 36, 28, 26, 33, 25, 35, 30, 37, 23, 27, 34, 29, 24, 31, 38, 41, 21, 39],
    #[0, 4, 3, 2, 1, 5, 6, 7, 8, 12, 11, 10, 9, 14, 13, 16, 15, 19, 20, 17, 18, 24, 22, 25, 21, 23, 26, 39, 32, 37, 30, 35, 28, 41, 34, 31, 40, 29, 38, 27, 36, 33],
    #[0, 4, 3, 2, 1, 6, 5, 8, 7, 11, 12, 9, 10, 13, 14, 15, 16, 20, 19, 18, 17, 39, 22, 35, 27, 31, 26, 24, 37, 32, 30, 25, 29, 36, 34, 23, 33, 28, 38, 21, 41, 40],
    #[0, 4, 3, 2, 1, 7, 8, 5, 6, 10, 9, 12, 11, 16, 15, 14, 13, 17, 18, 19, 20, 37, 22, 33, 29, 41, 26, 32, 39, 24, 30, 40, 27, 23, 34, 36, 35, 21, 38, 28, 31, 25],
    #[0, 4, 3, 2, 1, 8, 7, 6, 5, 9, 10, 11, 12, 15, 16, 13, 14, 18, 17, 20, 19, 32, 22, 40, 28, 36, 26, 37, 24, 39, 30, 33, 21, 31, 34, 41, 25, 27, 38, 29, 23, 35]]

@[expose] def a0T : Tab :=
  #[0, 1, 2, 3, 4, 6, 5, 8, 7, 10, 9, 12, 11, 14, 13, 16, 15, 18, 17, 20, 19, 27, 22, 31, 39, 35, 26, 21, 29, 28, 30, 23, 37, 40, 34, 25, 41, 32, 38, 24, 33, 36]

@[expose] def zT : Tab :=
  #[0, 6, 5, 8, 7, 9, 10, 11, 12, 2, 1, 4, 3, 16, 14, 13, 15, 19, 18, 20, 17, 31, 30, 21, 33, 32, 22, 27, 35, 39, 26, 23, 41, 36, 34, 40, 24, 29, 38, 37, 28, 25]

@[expose] def scanU1 : Bool :=
  let ES := enumBFS 42 gensS 20160
  let idx := indexOf ES.tabs
  allBelow uTabs.size fun i =>
    found idx ES.tabs uTabs[i]! && (uTabs[i]!)[0]! == 0 &&
      comp 42 uTabs[i]! uTabs[i]! == idTab 42

@[expose] def scanU2 : Bool :=
  let idx := indexOf uTabs
  allBelow uTabs.size fun i => allBelow uTabs.size fun j =>
    found idx uTabs (comp 42 uTabs[i]! uTabs[j]!)

@[expose] def scanU3 : Bool := found (indexOf uTabs) uTabs (idTab 42)

@[expose] def scanPU : Bool :=
  let ES := enumBFS 42 gensS 20160
  let idx := indexOf uTabs
  allBelow ES.tabs.size fun k =>
    !((ES.tabs[k]!)[0]! == 0) ||
      ((invTab 42 ES.tabs[k]!).size == 42 &&
        comp 42 (invTab 42 ES.tabs[k]!) ES.tabs[k]! == idTab 42 &&
        allBelow uTabs.size fun j =>
          found idx uTabs (conjTab 42 ES.tabs[k]! (invTab 42 ES.tabs[k]!) uTabs[j]!))

@[expose] def scanR : Bool :=
  let idx := indexOf uTabs
  comp 42 r₂T r₂T == idTab 42 &&
    allBelow uTabs.size fun j => found idx uTabs (conjTab 42 r₂T r₂T uTabs[j]!)

@[expose] def scanA0 : Bool :=
  let ES := enumBFS 42 gensS 20160
  let C := centTabs 42 ES.tabs r₂T
  found (indexOf uTabs) uTabs a0T && !(a0T == idTab 42) && found (indexOf C) C a0T

@[expose] def scanTrans : Bool :=
  let ES := enumBFS 42 gensS 20160
  allBelow uTabs.size fun j =>
    uTabs[j]! == idTab 42 ||
      anyBelow ES.tabs.size fun k =>
        (ES.tabs[k]!)[0]! == 0 && (invTab 42 ES.tabs[k]!).size == 42 &&
          comp 42 (invTab 42 ES.tabs[k]!) ES.tabs[k]! == idTab 42 &&
          conjTab 42 ES.tabs[k]! (invTab 42 ES.tabs[k]!) a0T == uTabs[j]!

@[expose] def scanZ : Bool :=
  let ES := enumBFS 42 gensS 20160
  let C := centTabs 42 ES.tabs r₂T
  found (indexOf C) C zT && zT[0]! == 0 && comp 42 (comp 42 zT zT) zT == idTab 42 &&
    !(zT == idTab 42) &&
    allBelow uTabs.size fun j =>
      !(comp 42 zT uTabs[j]! == comp 42 uTabs[j]! zT) || uTabs[j]! == idTab 42

@[expose] def scanRed : Bool :=
  let ES := enumBFS 42 gensS 20160
  let C := centTabs 42 ES.tabs r₂T
  let idx := indexOf uTabs
  allBelow C.size fun i =>
    !(comp 42 C[i]! C[i]! == idTab 42) ||
      anyBelow C.size fun j =>
        (invTab 42 C[j]!).size == 42 && comp 42 (invTab 42 C[j]!) C[j]! == idTab 42 &&
          found idx uTabs (conjTab 42 C[j]! (invTab 42 C[j]!) C[i]!)

@[expose] def scanWit : Bool :=
  allBelow uTabs.size fun j =>
    !(comp 42 r₂T uTabs[j]! == comp 42 uTabs[j]! r₂T) ||
      anyBelow uTabs.size fun i =>
        comp 42 (comp 42 (comp 42 r₂T uTabs[i]!) r₂T) uTabs[i]! == uTabs[j]!

end CFSG.QuasithinUnique.Id2519.Tab.A2
