module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P09K
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P09Reg
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P09Syl

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

section Step09


theorem node09_517 {G : Type} [Group G] [Finite G] {d : Data G} (h49 : d.Thm49Statement)
    (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    centralizerMod d.s56P10 d.s56U10 d.B ≤ centralizerMod d.s56P10 d.s56U11 d.F := by
  rintro p ⟨hp, -, hpB⟩
  refine ⟨hp, ?_, fun f hf => hd.s56_P10_comm_F_of_comm_B h49 hz hp hpB f hf⟩
  exact Subgroup.centralizer_le_normalizer (d.s56U11 : Set G) (mem_centralizer_iff.2 fun u hu =>
    (hd.s56_P0_comm_U11 h49 (Data.s56_P10_le_P0 d hp) hu).symm)

theorem step09_of_518
    (h518 : ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}, d.Thm49Statement → d.Hyp →
      d.S56Z0 z₀ → d.S56Kappa → ⁅d.s56P10, d.F⁆ ≤ d.s56U11) : Step09 := by
  intro G _ _ d z₀ h49 hd hz hκ h05 h07 h08
  have h18 := h518 h49 hd hz hκ
  obtain ⟨h3, h4, h5, h6, h7⟩ := node09_519 h49 hd h18
  exact ⟨node09_517 h49 hd hz, h18, h3, h4, h5, h6, h7, node09_syl h49 hd hz⟩

theorem step09_holds : Step09 :=
  step09_of_518 fun h49 hd hz hκ => node09_518 h49 hd hz hκ

end Step09

end CFSG.LocalAnalysis.EvenBN.Tits.N
