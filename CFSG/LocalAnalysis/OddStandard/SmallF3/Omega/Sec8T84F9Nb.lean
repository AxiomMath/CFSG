module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec8t84_gamma_not_cent (hSw : Sec8T84OuterSwaps) {t : G} {L S : Subgroup G} {z g : G}
    {B E T : Subgroup G} (hE : Sec8E G t L S z g B E) (hTE : T ≤ normalizer (E : Set G))
    {γ : G} (hout : InducesOutsideGStar L 6 (-1) γ) :
    γ ∉ T ⊓ centralizer ({t} : Set G) := by
  rintro hγ
  have hγT : γ ∈ T := hγ.1
  have hγC : γ ∈ centralizer ({t} : Set G) := hγ.2
  have hγNE : γ ∈ normalizer (E : Set G) := hTE hγT
  have hγNB : γ ∈ normalizer (B : Set G) := by
    rw [← hE.cent_t]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hγNE, Subgroup.le_normalizer hγC⟩
  have hout' : InducesOutsideGStar L 6 (-1) γ := hout
  obtain ⟨V, _, _, _, Q, hQ, e, x, -, -, hind, -, -⟩ := hout'
  have hγNL : γ ∈ normalizer (L : Set G) := hind.1
  have hOm6M : IsOm6M L := ⟨hE.ctx.component.isQuasisimple, hE.ctx.omega6m⟩
  exact hSw G L hOm6M γ hγNL hout B (hE.ctx.B_le.trans inf_le_left) hE.ctx.B_e16 hγNB

end CFSG.OddStandard.SmallF3.Omega
