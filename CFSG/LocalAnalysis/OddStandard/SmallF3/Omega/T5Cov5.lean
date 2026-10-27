module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Asm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov5Model

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem asc82Tab5_cover_i4_kind5_of (hS : Asc82SchurU43) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 5 →
        ∃ u ∈ XOut L s, orderOf u = 2 ∧ IsI4PlusIn L u ∧ s * u ∈ conjClassIn L s := by
  intro G _ _ L hL s hs _ hk
  obtain ⟨V, i1, i2, i3, Q, hQ, e, x, hdim, hsgn, hx, hx2, hxn⟩ := hk
  obtain ⟨ρ, hρx, hρ, hρρ⟩ := ff6m_K4_split hQ hdim hsgn hx2 hxn
  obtain ⟨φ, hφ, -, hact⟩ := t5_cover_data hS hL hdim hsgn hx hρx
  obtain ⟨w, hw, hww, hwt, c, hc⟩ := t5_cov5_model hQ hdim hsgn hρ hρρ
  exact t5c_cover_i4_of_model hL hφ hs hact hw hww hwt hc

end CFSG.OddStandard.SmallF3.Omega
