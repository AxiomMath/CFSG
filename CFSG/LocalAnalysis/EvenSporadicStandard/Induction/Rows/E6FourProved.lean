module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BRowFacts
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.LieType.Simplicity.LieModelFinite
public import CFSG.RankThree.PerfectCover.HopfCentralCoversUnrestricted
public import CFSG.GH74.Generic.GKFCover

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.Multiplier

theorem card_table_e6_four :
    Nat.card (generic .E6 0 2 2 × exceptional .E6 0 2 2) = 3 := by
  have h1 : genericOrders .E6 0 2 2 = (Nat.gcd 3 (2 ^ 2 - 1), 1) := rfl
  have h2 : exceptionalOrders .E6 0 2 2 = (1, 1) := rfl
  have h3 : Nat.gcd 3 (2 ^ 2 - 1) = 3 := by norm_num
  unfold generic exceptional
  rw [h1, h2, h3]
  simp

section Cover

theorem e6FourNoEvenCover_proved : E6FourNoEvenCover := by
  rintro N _ hN ⟨Q₀, _, hq, hev, ⟨e⟩⟩
  have hfin : Finite N := CFSG.LieType.Simplicity.finite_of_native_lieModel hN
  have : Finite Q₀ :=
    CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hq e
  obtain ⟨-, hch⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hN (by decide)
  obtain ⟨-, ⟨f⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessNative.e6_row hch
  have h1 := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  have h2 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier N) = 3 := by
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess N).toEquiv,
      Nat.card_congr f.toEquiv]
    exact card_table_e6_four
  rw [h2] at h1
  exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat (by decide : Odd 3) h1)) hev

end Cover

end CFSG.EvenSporadicStandard.Induction.Hyp
