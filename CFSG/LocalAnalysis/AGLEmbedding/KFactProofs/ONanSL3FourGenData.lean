module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen

open CFSG.PSL3Four.Native

@[expose] def tA : Tab :=
  #[0, 11, 9, 10, 12, 5, 8, 6, 7, 18, 17, 20, 19, 16, 14, 13, 15, 3, 2, 4, 1, 25, 22, 21, 24, 23,
    30, 36, 29, 39, 34, 32, 41, 27, 26, 40, 33, 35, 38, 28, 37, 31]

@[expose] def tB : Tab :=
  #[2, 1, 3, 0, 4, 9, 6, 19, 16, 17, 14, 11, 8, 13, 18, 7, 12, 5, 10, 15, 20, 21, 31, 33, 32, 30,
    26, 27, 28, 29, 36, 35, 37, 34, 23, 22, 25, 24, 41, 39, 38, 40]

@[expose] def tZ : Tab :=
  #[14, 1, 18, 10, 6, 0, 13, 15, 16, 2, 17, 11, 8, 4, 5, 19, 12, 3, 9, 7, 20, 26, 38, 34, 22, 30,
    27, 21, 28, 29, 36, 41, 31, 23, 33, 40, 25, 35, 24, 39, 37, 32]

@[expose] def hGens : Array Tab := #[tA, tB]

@[expose] def mGens : Array (Array Tab) :=
  #[#[tZ, tA], #[tZ, tB], #[tZ, comp 42 tA tB], #[tZ, comp 42 (comp 42 tA tB) tB]]

@[expose] def memT (T : Array Tab) (x : Tab) : Bool := anyBelow T.size fun k => T[k]! == x

@[expose] def commT (x y : Tab) : Bool := comp 42 x y == comp 42 y x

@[expose] def mEnum (k : Nat) : Enum := enumBFS 42 mGens[k]! 9

@[expose] def fixTabs (ES T : Array Tab) : Array Tab :=
  ES.filter fun s => anyBelow T.size fun m => !(T[m]! == idTab 42) && commT s T[m]!

@[expose] def fixGens (ES : Array Tab) (k : Nat) : Array Tab := fixTabs ES (mEnum k).tabs

@[expose] def genCheck (G : Array Tab) : Bool :=
  let E := enumBFS 42 G 20160
  enumOK 42 G E && E.tabs.size == 20160

@[expose] def sl3GenCheck (ES ER : Array Tab) : Bool :=
  let EH := enumBFS 42 hGens 27
  let H := EH.tabs
  let idxH := indexOf H
  memT ER tA && memT ER tB && enumOK 42 hGens EH && H.size == 27 &&
    (allBelow 4 fun k => allBelow (mGens[k]!).size fun j => found idxH H (mGens[k]!)[j]!) &&
    (allBelow 4 fun k => enumOK 42 mGens[k]! (mEnum k) && (mEnum k).tabs.size == 9) &&
    (allBelow H.size fun i => allBelow H.size fun j => !commT H[i]! H[j]! ||
      anyBelow 4 fun k => found (indexOf (mEnum k).tabs) (mEnum k).tabs H[i]! &&
        found (indexOf (mEnum k).tabs) (mEnum k).tabs H[j]!) &&
    memT ES tZ && memT ES tA &&
    (allBelow 3 fun k => genCheck (fixGens ES (k + 1)))

end CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen
