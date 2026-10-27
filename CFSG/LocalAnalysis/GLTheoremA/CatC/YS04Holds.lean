module

public import CFSG.LocalAnalysis.GLTheoremA.YS04Final
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD26e
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KD26d
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04G
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04F

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4


theorem ys04_holds
    (hD4 : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → I117D4UsedAt G)
    (hbc : KD26bc) (hf : KD26f) : YS04 :=
  ys04_of_kd26 kdOut_holds hD4 hbc CatB.kd26d_holds kd26e_holds hf kd26g_holds kd26h_holds

theorem ys04_holds_of_simple
    (hD4 : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → I117D4UsedAt G)
    (hbc : KD26bcSimple) (hf : KD26fSimple) : YS04 :=
  ys04_holds hD4 (kd26bc_of_simple hbc) (kd26f_of_simple hf)

theorem ys04_holds_of_E6
    (hD4 : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → I117D4UsedAt G)
    (hbc : KD26bcSimple) (hE6 : YS04F.KD26fE6) : YS04 :=
  ys04_holds_of_simple hD4 hbc (YS04F.kd26fSimple_of_E6 hE6)

end CFSG.LocalAnalysis.GLTheoremA
