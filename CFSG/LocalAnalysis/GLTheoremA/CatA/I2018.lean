module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Spor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Lie
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Alt
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThree
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Two
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fi24
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fi23
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Co1
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Co2
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Co3
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.HN
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.J4
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Ly
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.McLON
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Suz
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporJ3
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporLy
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporSuz
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4O2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Cent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Spor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs103
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2018

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator.YS08
open scoped commutatorElement

section SporadicLeaves

theorem sporL3Down_all_of_BM (hB : SporL3Down TauCeti.SporadicName.B)
    (hM : SporL3Down TauCeti.SporadicName.M) : ∀ s : TauCeti.SporadicName, SporL3Down s := by
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo :=
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  intro s
  cases s with
  | M11 => exact sporL3Down_of_inner hOut (sporL3DownInner_M11 hbr)
  | M12 => exact sporL3Down_of_inner hOut (sporL3DownInner_M12 hbr)
  | M22 => exact sporL3Down_of_inner hOut (sporL3DownInner_M22 hbr)
  | M23 => exact sporL3Down_of_inner hOut (sporL3DownInner_M23 hbr)
  | M24 => exact sporL3Down_of_inner hOut (sporL3DownInner_M24 hbr)
  | J1 => exact sporL3Down_of_inner hOut (sporL3DownInner_J1 hbr)
  | J2 => exact sporL3Down_of_inner hOut (sporL3DownInner_J2 hbr)
  | J3 => exact sporL3Down_of_inner hOut (sporL3DownInner_J3 hbr)
  | J4 => exact sporL3Down_of_inner hOut (sporL3DownInner_J4 hbr)
  | HS => exact sporL3Down_of_inner hOut (sporL3DownInner_HS hbr)
  | McL => exact sporL3Down_of_inner hOut (sporL3DownInner_McL hbr)
  | He => exact sporL3Down_of_inner hOut (sporL3DownInner_He hbr)
  | Ru => exact sporL3Down_of_inner hOut (sporL3DownInner_Ru hbr)
  | Suz => exact sporL3Down_of_inner hOut (sporL3DownInner_Suz hbr)
  | ONan => exact sporL3Down_of_inner hOut (sporL3DownInner_ONan hbr)
  | Co1 => exact sporL3Down_of_inner hOut (sporL3DownInner_Co1 hbr)
  | Co2 => exact sporL3Down_of_inner hOut (sporL3DownInner_Co2 hbr)
  | Co3 => exact sporL3Down_of_inner hOut (sporL3DownInner_Co3 hbr)
  | Fi22 => exact sporL3Down_of_inner hOut (sporL3DownInner_Fi22 hbr)
  | Fi23 => exact sporL3Down_of_inner hOut (sporL3DownInner_Fi23 hbr)
  | Fi24Prime => exact sporL3Down_of_inner hOut (sporL3DownInner_Fi24 hbr)
  | HN => exact sporL3Down_of_inner hOut (sporL3DownInner_HN hbr)
  | Ly => exact sporL3Down_of_inner hOut (sporL3DownInner_Ly hbr)
  | Th => exact sporL3Down_of_inner hOut (CFSG.HardMathSupport.Dickson.Sec6.th_sporL3DownInner hbr)
  | B => exact hB
  | M => exact hM

theorem i2018At_of_facts {G : Type} [Group G] [Finite G]
    (hB : SporL3Down TauCeti.SporadicName.B) (hM : SporL3Down TauCeti.SporadicName.M)
    (hOdd : I2018OddB3) (hChar : I2018U38Char2) (hNA : I2018U38NotAlt) (hCover : I2018U38Cover)
    (hBT : I2018BorelTits) (hCore : I2018ChevCore) : I2018At G := by
  intro _ x K J S₀ hK hX _ hx3 _ hJ hJU hS₀K hS₀2 hJS₀ hS₀n hxN
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hK
  haveI := hsimple
  have hcat : IsCatalogGroup (PSimple 3 K) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' ((hX.of_le hK.1).quotient _)
      (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK)
  obtain ⟨i, ⟨eS⟩⟩ := hcat
  have hSpor := sporL3Down_all_of_BM hB hM
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    apply eS.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exact (i2018_alt_absurd hK hxN hx3 hJ hJU hNA hn eS).elim
  | sporadic s =>
    exact (i2018_spor_absurd hK hxN hx3 hJ hJU hCover (hSpor s) eS).elim
  | lie dl =>
    exact i2018_lie hOdd hChar hBT hCore hK hxN hx3 hJ hJU hS₀K hS₀2 hJS₀ hS₀n dl.1.characteristic
      (up7a8_char_prime dl.1) (Or.inl ⟨TauCeti.CFSGIndex.lie dl, rfl, ⟨eS⟩⟩)

end SporadicLeaves

end CFSG.LocalAnalysis.GLTheoremA.I2018

end
