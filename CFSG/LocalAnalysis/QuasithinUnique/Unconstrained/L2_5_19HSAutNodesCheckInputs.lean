module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutData
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSA6Inputs
public import CFSG.Sporadic.SmallOddCore.HSCheckInputs
public import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.QuasithinUnique.Id2519.HSAut
open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.QuasithinUnique.Id2519.UHS

@[expose] def wordTab (ls : List Nat) : Tab :=
  (ls.map letterArr).foldr (comp 3850) (idTab 3850)

@[expose] def y1Tab : Tab := wordTab y1Letters

@[expose] def y2Tab : Tab := wordTab y2Letters

@[expose] def cTab : Tab := wordTab cLetters

@[expose] def a0Tab : Tab := letterArr 0

@[expose] def eTab : Tab :=
  (eLetters.map fun l => if l = 0 then y1Tab else y2Tab).foldr (comp 3850) (idTab 3850)

@[expose] def gTab : Tab := wordTab gLetters

@[expose] def giTab : Tab := invTab 3850 gTab

@[expose] def gensA0 : Array Tab := #[natArr (hsCentTbl 6), natArr (hsCentTbl 7)]

@[expose] def enumA0 : Enum := enumBFS 3850 gensA0 7680

@[expose] def r1T : Table := hexT 3 3850 0 r1Hex

@[expose] def r1Tab : Tab := natArr r1T

@[expose] def chkSizes : Bool :=
  (allBelow 3 fun l => (letterArr l).size == 3850) &&
    (allBelow 2 fun l => CFSG.Sporadic.SmallOddCore.permOK 3850 (hsCentTbl (6 + l)) &&
      (hsCentTbl (6 + l)).size == 3850) &&
    CFSG.Sporadic.SmallOddCore.permOK 3850 hsOuterTbl &&
    CFSG.Sporadic.SmallOddCore.permOK 3850 r1T && r1T.size == 3850

@[expose] def chkEnum : Bool := enumOK 3850 gensA0 enumA0 && enumA0.tabs.size == 7680

@[expose] def chkConj : Bool :=
  comp 3850 gTab a0Tab == comp 3850 eTab gTab && giTab.size == 3850 &&
    comp 3850 giTab gTab == idTab 3850

@[expose] def scanTab (k : Nat) : Tab := conjTab 3850 gTab giTab enumA0.tabs[k]!

@[expose] def scanRow (k : Nat) : Bool :=
  !(comp 3850 (scanTab k) y1Tab == comp 3850 y1Tab (scanTab k) &&
      comp 3850 (scanTab k) y2Tab == comp 3850 y2Tab (scanTab k)) ||
    scanTab k == idTab 3850 || scanTab k == cTab

@[expose] def chkScan : Bool := allBelow enumA0.tabs.size scanRow

@[expose] def chkR1 : Bool :=
  comp 3850 r1Tab r1Tab == idTab 3850 &&
    comp 3850 r1Tab y1Tab == comp 3850 y1Tab r1Tab &&
    comp 3850 r1Tab y2Tab == comp 3850 y2Tab r1Tab &&
    !hsSift r1T && hsSift (compT 3850 r1T hsOuterTbl)

@[expose] def nodesCheck : Bool := chkSizes && chkEnum && chkConj && chkScan && chkR1

end CFSG.QuasithinUnique.Id2519.HSAut
