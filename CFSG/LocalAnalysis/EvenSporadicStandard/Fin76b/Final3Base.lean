
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma65
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinEJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ2Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ2
public import CFSG.Sporadic.SmallOddCore.J2DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsBridge
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinEJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ3Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ3
public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5J2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5J3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.SwapY
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.KleinNoSwap
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J2E
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J3E
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J2
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelInvolutionFusion

@[expose] public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

def Fin76bSwapInCentralizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → ∀ y ∈ normalizer (E : Set G), y * β = β * y → y * z * y⁻¹ = z * t →
      y * t * y⁻¹ = t → ∃ m ∈ centralizer (E : Set G), m * z * m⁻¹ = z * t

def Fin76bSwapInnerOnD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → ∀ y ∈ normalizer (E : Set G), y * β = β * y → y * z * y⁻¹ = z * t →
      y * t * y⁻¹ = t → ∃ d ∈ E ⊓ centralizer ({β} : Set G),
        ∀ e ∈ E ⊓ centralizer ({β} : Set G), y * e * y⁻¹ = d * e * d⁻¹

def Fin76bAutE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → ∀ y ∈ normalizer (E : Set G), y * β = β * y →
      (∃ d ∈ E ⊓ centralizer ({β} : Set G),
        ∀ e ∈ E ⊓ centralizer ({β} : Set G), y * e * y⁻¹ = d * e * d⁻¹) →
      ∃ d ∈ E ⊓ centralizer ({β} : Set G), ∃ j : ℤ,
        ∀ e ∈ E, y * e * y⁻¹ = (d * β ^ j) * e * (d * β ^ j)⁻¹

theorem fin76bSwapInCentralizer_of_innerOnD_autE (h1 : Fin76bSwapInnerOnD) (h2 : Fin76bAutE) :
    Fin76bSwapInCentralizer := by
  intro G _ _ L z t T₀ E Q x β B hconf hW y hyN hyβ hyz hyt
  have hcfg := hconf.cfg
  have hβL : β ∈ L := hconf.B_le hconf.beta_mem
  have hβt : β * t = t * β := mem_centralizer_singleton_iff.1 (hconf.B_cent hconf.beta_mem)
  have hβz : β * z = z * β := hcfg.z_comm_of_mem_A hβL
  obtain ⟨d, hdD, j, hj⟩ := h2 G L z t T₀ E Q x β B hconf hW y hyN hyβ
    (h1 G L z t T₀ E Q x β B hconf hW y hyN hyβ hyz hyt)
  have hdE : d ∈ E := hdD.1
  have hdz : d * z = z * d := hcfg.z_comm_of_mem_A (hconf.econfig.le.trans hcfg.T₀_le hdE)
  have hdt : d * t = t * d := hcfg.t_central d (hconf.econfig.le hdE)
  have hbz : β ^ j * z = z * β ^ j := ((show Commute β z from hβz).zpow_left j).eq
  have hbt : β ^ j * t = t * β ^ j := ((show Commute β t from hβt).zpow_left j).eq
  have huz : (d * β ^ j) * z = z * (d * β ^ j) := by
    rw [mul_assoc, hbz, ← mul_assoc, hdz, mul_assoc]
  have hut : (d * β ^ j) * t = t * (d * β ^ j) := by
    rw [mul_assoc, hbt, ← mul_assoc, hdt, mul_assoc]
  have huzt : (d * β ^ j) * (z * t) = (z * t) * (d * β ^ j) := by
    calc (d * β ^ j) * (z * t) = ((d * β ^ j) * z) * t := by group
      _ = (z * (d * β ^ j)) * t := by rw [huz]
      _ = z * ((d * β ^ j) * t) := by group
      _ = z * (t * (d * β ^ j)) := by rw [hut]
      _ = (z * t) * (d * β ^ j) := by group
  refine ⟨(d * β ^ j)⁻¹ * y, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro e he
    have := hj e he
    calc e * ((d * β ^ j)⁻¹ * y) = (d * β ^ j)⁻¹ * ((d * β ^ j) * e * (d * β ^ j)⁻¹) * y := by
          group
      _ = (d * β ^ j)⁻¹ * (y * e * y⁻¹) * y := by rw [this]
      _ = (d * β ^ j)⁻¹ * y * e := by group
  · calc (d * β ^ j)⁻¹ * y * z * ((d * β ^ j)⁻¹ * y)⁻¹
        = (d * β ^ j)⁻¹ * (y * z * y⁻¹) * (d * β ^ j) := by group
      _ = (d * β ^ j)⁻¹ * (z * t) * (d * β ^ j) := by rw [hyz]
      _ = (d * β ^ j)⁻¹ * ((z * t) * (d * β ^ j)) := by group
      _ = (d * β ^ j)⁻¹ * ((d * β ^ j) * (z * t)) := by rw [huzt]
      _ = z * t := by group

theorem fin76bNoKleinFour_of_swapInCentralizer (h : Fin76bSwapInCentralizer) :
    Fin76bNoKleinFour := by
  intro G _ _ L z t T₀ E Q x β B hconf hW S hS2 hSC hSmax hzS hBS hSV
  have hcfg := hconf.cfg
  have hE := hconf.econfig
  obtain ⟨y, hyN, hyβ, hyz, hyt⟩ := exists_swap_centralizing_beta hconf hW
  obtain ⟨m, hmM, hmz⟩ := h G L z t T₀ E Q x β B hconf hW y hyN hyβ hyz hyt
  subst hSV
  have hzt : z ≠ t := fun h => hcfg.z_not_mem_A (h ▸ hcfg.t_mem_A)
  refine klein_sylow_no_swap (M := centralizer (E : Set G)) hcfg.z_sq hcfg.t_sq hcfg.z_ne
    hcfg.t_ne hzt hcfg.t_comm_z.symm (hE.z_mem_centralizer hcfg) (hE.t_mem_centralizer hcfg)
    (fun m hm => (mem_centralizer_iff.1 hm t hE.t_mem).symm) hS2 hSmax hmM hmz

end CFSG.EvenSporadicStandard.Fin76b
