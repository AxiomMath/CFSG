module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE81
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

section Holds


theorem u42SLevel_of_residuals (hE81C : U42E81CentAt) (hE81I : U42E81InnU6At)
    (hE27C : U42E27CentAt) (hE27L : U42E27LocAt) : U42SLevel :=
  ⟨u42E81At_of_residuals hE81C hE81I, u42E27At_of_residuals hE27C hE27L, u42RankAt_holds⟩

end Holds

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat
