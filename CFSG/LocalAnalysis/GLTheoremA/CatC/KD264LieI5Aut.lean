module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5AutTri
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5AutL28
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5AutU38

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

section I5Holds


theorem kd264I5Aut_holds : KD264I5Aut := by
  intro e _
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨q, he, hq3⟩
    exact kd264I5Aut_triality e q he hq3
  · rintro ⟨q, he, hq8⟩
    exact kd264I5Aut_l28 e q he hq8
  · rintro ⟨q, he, hq8⟩
    exact kd264I5Aut_u38 e q he hq8

end I5Holds

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
