module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutClass
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutData
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.SmallOddCore.HSData

public section

namespace CFSG.QuasithinUnique.Id2519.HSAut
open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native

@[expose] def qGenT (l : Nat) : Table := hsCentTbl (22 + l)

@[expose] def qWordTab (ls : List Nat) : Tab :=
  (ls.map fun l => natArr (qGenT l)).foldr (comp 3850) (idTab 3850)

@[expose] def e1Tab : Tab := qWordTab e1Letters

@[expose] def e2Tab : Tab := qWordTab e2Letters

@[expose] def gensE : Array Tab := #[e1Tab, e2Tab]

@[expose] def ginvE : Array Tab := gensE.map (invTab 3850)

@[expose] def enumE : Enum := enumBFS 3850 gensE 20160

@[expose] def classE : ClassData := classData 3850 enumE.tabs classSizes

@[expose] def outerCheck : Bool :=
  (allBelow 4 fun l =>
      CFSG.Sporadic.SmallOddCore.permOK 3850 (qGenT l) && (qGenT l).size == 3850) &&
    enumOK 3850 gensE enumE && enumE.tabs.size == 20160 &&
    classOKGen 3850 enumE.tabs gensE ginvE classE classSizes

end CFSG.QuasithinUnique.Id2519.HSAut
