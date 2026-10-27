module

public import CFSG.GH74.GLS.Stage1.Main.RankG2Proof
public import CFSG.RankThree.PartOne.S11c.G2Plane

public section

namespace CFSG.GH74.GLS.Stage1.Main

theorem rankG2_thm
    : RankG2 :=
  rankG2_of_elemTwo (fun K _ _ hK R hR _ _ => (CFSG.RankThree.PartOne.g2_elementary_two hK hR).1)

end CFSG.GH74.GLS.Stage1.Main
