module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.Assembly
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblySO
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyExc
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Assembly

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Yardstones.Md42047359a2a


theorem lieSemisimpleCent : CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimpleCent := by
  intro S _ _ hs hnc idx he p hp hp2 hpq β hβ hβ1
  cases hf : lieFamily idx.1
  · exact lieSemisimpleCentLinearUnitary S hs hnc idx hf he p hp hp2 hpq β hβ hβ1
  · exact lieSemisimpleCentSymplecticOrthogonal S hs hnc idx hf he p hp hp2 hpq β hβ hβ1
  · exact lieSemisimpleCentExceptional S hs hnc idx hf he p hp hp2 hpq β hβ hβ1
  · exact CFSG.HardMathSupport.Dickson.SuzukiReeB.lieSemisimpleCentSuzukiReeTits S hs hnc idx hf
      he p hp hp2 hpq β hβ hβ1

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
