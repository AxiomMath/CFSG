module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard03Red
public import CFSG.LocalAnalysis.ComponentClassification.GSYard03Join
public import CFSG.LocalAnalysis.ComponentClassification.GSYard03L4U4Leaf
public import CFSG.LocalAnalysis.ComponentClassification.GSYard03Alt
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard03

theorem quasisimpleCentralSquareFour_holds :
    QuasisimpleCentralSquareFour :=
  quasisimpleCentralSquareFour_of_leaves f1LeafL4_holds f1LeafU4_holds f1LeafSz8_holds
    f1LeafAlt_holds f1LeafM12_holds

theorem solomonQTwoDisconnectedSylowInvFor_holds :
    SolomonQTwoDisconnectedSylowInvFor :=
  solomonQTwoDisconnectedSylowInvFor_of_leaves centralInvolutionJoin
    GSYard02.quasisimpleSylowFourJoinedSCN_holds quasisimpleCentralSquareFour_holds

end CFSG.ComponentClassification.Sol76.Sig.GSYard03
