module

public import CFSG.LocalAnalysis.GLTheoremA.YS04Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD2028Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I71
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26Certified

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB


theorem ys04_of_kd
    (hSU3 : KDSU3) (hOut : KDOut)
    (hD4 : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → I117D4UsedAt G)
    (h2611 : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
      I2611UsedAt G p) : YS04 :=
  ys04_of_remaining fun G _ _ m hctx p hp =>
    ⟨i1411At_holds hp.1.1,
      i113UsedAt_of_kd HardMathSupport.Timmesfeld.Coordinator.tables112_holds
          HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
          HardMathSupport.Solomon.Coordinator.tables112Types_holds
          HardMathSupport.Solomon.Coordinator.tables112More_holds kd2028_holds hSU3 hctx.1.simple
          hctx.1.kProper hp.1.1 hp.1.2.1,
      i71UsedAt_of_kd hOut (hD4 G m hctx) hctx.1.simple hctx.1.nonabelian hctx.1.kProper hp.1.1
        hp.1.2.1,
      h2611 G m hctx p hp⟩

theorem ys04_of_kdOut
    (hOut : KDOut)
    (hD4 : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → I117D4UsedAt G)
    (h2611 : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
      I2611UsedAt G p) : YS04 :=
  ys04_of_kd kdSU3_holds hOut hD4 h2611

theorem ys04_of_kd26
    (hOut : KDOut)
    (hD4 : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → I117D4UsedAt G)
    (hbc : KD26bc) (hd : KD26d) (he : KD26e) (hf : KD26f) (hg : KD26g) (hh : KD26h) : YS04 :=
  ys04_of_kdOut hOut hD4 fun _ _ _ _ hctx _ hp =>
    i2611UsedAt_of_kd kd26a_holds hbc hd he hf hg hh hctx.1.simple hctx.1.nonabelian
      hctx.1.kProper hp.1.1 hp.1.2.1

end CFSG.LocalAnalysis.GLTheoremA
