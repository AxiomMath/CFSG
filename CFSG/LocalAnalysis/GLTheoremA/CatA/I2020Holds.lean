module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020Reduce
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020LinInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020LinOuter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020UniInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020UniOuter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020OrthInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020D4Three
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020D4Graph
public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat22

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020


theorem i2020Res_holds : I2020Res :=
  ⟨i2020At_of_parts i2020LinInner i2020LinOuter i2020UniInner i2020UniOuter i2020OrthInner
    i2020OrthOuter (i2020D4Three_of_graphType i2020D4GraphType_holds)⟩

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
