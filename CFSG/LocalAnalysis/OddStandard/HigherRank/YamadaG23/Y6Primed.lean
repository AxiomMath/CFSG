module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec5S
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec6S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three

@[expose] def Sec61' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.toCtx5.Facts5 → c.Fact61

@[expose] def Sec62' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.toCtx5.Facts5 → c.Fact62

@[expose] def Sec63' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.toCtx5.Facts5 → c.Fact61 → c.Fact62 → c.Fact63

@[expose] def Sec64a' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.toCtx5.Facts5 → c.Facts6 → c.Four1 ∧ c.Four2 ∧ c.Four3

@[expose] def Sec64b' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.toCtx5.Facts5 → c.Facts6 → c.Four4

theorem sec61_of (h5 : Sec5) (h : Sec61') : Sec61 :=
  fun G _ _ L hS hL c => h G L hS hL c (h5 G L hS hL c.toCtx5)

theorem sec62_of (h5 : Sec5) (h : Sec62') : Sec62 :=
  fun G _ _ L hS hL c => h G L hS hL c (h5 G L hS hL c.toCtx5)

theorem sec63_of (h5 : Sec5) (h61 : Sec61') (h62 : Sec62') (h : Sec63') : Sec63 :=
  fun G _ _ L hS hL c =>
    h G L hS hL c (h5 G L hS hL c.toCtx5) (h61 G L hS hL c (h5 G L hS hL c.toCtx5))
      (h62 G L hS hL c (h5 G L hS hL c.toCtx5))

theorem sec6_of_primed (h5 : Sec5) (h61 : Sec61') (h62 : Sec62') (h63 : Sec63') : Sec6 :=
  sec6_of (sec61_of h5 h61) (sec62_of h5 h62) (sec63_of h5 h61 h62 h63)

theorem sec64a_of (h5 : Sec5) (h6 : Sec6) (h : Sec64a') : Sec64a :=
  fun G _ _ L hS hL c => h G L hS hL c (h5 G L hS hL c.toCtx5) (h6 G L hS hL c)

theorem sec64b_of (h5 : Sec5) (h6 : Sec6) (h : Sec64b') : Sec64b :=
  fun G _ _ L hS hL c => h G L hS hL c (h5 G L hS hL c.toCtx5) (h6 G L hS hL c)

end CFSG.OddStandard.HigherRank.YamadaG23
