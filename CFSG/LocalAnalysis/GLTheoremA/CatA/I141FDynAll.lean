module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynTri

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10GField

section ComponentType


theorem compTypeLie2_holds : CompTypeLie2 := by
  intro S _ _ labL β p hp hp2 hcen hin hβp hβ1 hG2 hB2der hG2der htwF4der htwB2 J hJ
  rcases fam_cover labL with hF | hF | hF | hF | hF
  · exact Cls.compType_lin hp hp2 hcen hF hin hβp hJ
  · exact Cls.compType_uni hp hp2 hcen hF hin hβp hJ
  · rcases hF with hB | hC | hB2
    · exact Cls.compType_symp hp hp2 hcen (Or.inl hB) hin hβp hJ
    · exact Cls.compType_symp hp hp2 hcen (Or.inr hC) hin hβp hJ
    · exact (hB2der hB2).elim
  · exact Cls.compType_orth hp hp2 hcen hF hin hβp hJ
  · rcases hF with hE6 | hE7 | hE8 | hF4 | htwE6 | htriD4 | hG2c | hG2derc | htwB2c |
      htwF4c | htwF4derc
    · exact Exc.compType_E hp hp2 hcen hin hβp hβ1 (Or.inl hE6) hJ
    · exact Exc.compType_E hp hp2 hcen hin hβp hβ1 (Or.inr (Or.inl hE7)) hJ
    · exact Exc.compType_E hp hp2 hcen hin hβp hβ1 (Or.inr (Or.inr hE8)) hJ
    · exact Exc.compType_F4 hp hp2 hcen hin hβp hβ1 hF4 hJ
    · exact Exc.compType_twE6 hp hp2 hcen hin hβp hβ1 htwE6 hJ
    · exact Tri.compType_triD4 hp hp2 hcen hin hβp hβ1 htriD4 hJ
    · exact (hG2 hG2c).elim
    · exact (hG2der hG2derc).elim
    · exact (htwB2 htwB2c).elim
    · exact Tri.compType_twF4 hp hp2 hcen hin hβp hβ1 htwF4c hJ
    · exact (htwF4der htwF4derc).elim

end ComponentType

section Head


theorem i141DynkinLie_holds : I141DynkinLie :=
  i141DynkinLie_of_compTypeLie2 compTypeLie2_holds

end Head

end CFSG.LocalAnalysis.GLTheoremA.I141F
