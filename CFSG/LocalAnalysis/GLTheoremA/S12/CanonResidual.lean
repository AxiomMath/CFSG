module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonMain
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Aut
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriHolds
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonL2Holds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Residual



theorem TriResidualFacts.toTriFacts (h : TriResidualFacts) : TriFacts :=
  ⟨triD4Schur_holds, triD4Rank_holds, h.cent, h.lemmaJ, h.noG2, l2Rank3_holds, h.u3L, h.u3Torus⟩

namespace S12

theorem canonNbrAt_of_residual_facts (F6 : E6FourResidualFacts) (F3 : TriResidualFacts) {G : Type}
    [Group G] [Finite G] {m p : ℕ} (hc : S12Ctx G m p) (h171 : I171OneAt G) : CanonNbrAt G p :=
  canonNbrAt_of_facts F6.toE6FourFacts F3.toTriFacts hc h171

end S12

end Residual

end CFSG.LocalAnalysis.GLTheoremA
