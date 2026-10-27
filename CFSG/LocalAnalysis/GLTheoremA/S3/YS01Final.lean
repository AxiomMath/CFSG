module

public import CFSG.LocalAnalysis.GLTheoremA.S3.YS01Schreier
public import CFSG.LocalAnalysis.GLTheoremA.S3.KMMain
public import CFSG.LocalAnalysis.GLTheoremA.S3.I112L227

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4


theorem ys01_of_catalogue
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
      I1135At G p ∧ ChevClosureAt G p ∧ ChevUniqueAt G p ∧ ChevInnerAt G p ∧ I65At G p ∧
        I76At G p ∧ ChevRank3At G p ∧ L227DataAt G ∧ L227PumpAt G) : YS01 :=
  ys01_of_remaining kmUsedAt_holds fun G _ _ m hctx p hp =>
    let h := hin G m hctx p hp
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      i112L227At_holds hctx.1.simple hctx.1.kProper, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

end CFSG.LocalAnalysis.GLTheoremA
