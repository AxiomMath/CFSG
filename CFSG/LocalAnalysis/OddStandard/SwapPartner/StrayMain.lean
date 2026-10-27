module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TrichotomyStray
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayQuasi

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

theorem hStray_of_swapShape (hF : DihedralOuterInvolutionFact) {X : Type} [Group X] [Finite X]
    {t : X} {Sg V : Subgroup X} (h : SwapShape t Sg V) :
    ∀ J : Subgroup X, CFSG.IsComponent J → ⁅(⁅Sg, Sg⁆ : Subgroup X), J⁆ = ⊥ → t ∈ J := by
  intro J hJ hJA
  have ht2 : t ^ 2 = 1 := h.sq_eq_one
  have htN : t ∈ normalizer (J : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (SwapShape.map_conj_eq_of_stray h hJ hJA)
  have h4 : 4 ≤ Nat.card ↥(J ⊓ centralizer ({t} : Set X)) :=
    four_le_card_inf_centralizer_of_normalizer hF hJ.1 ht2 htN
  exact SwapShape.mem_of_stray_of_four_le h hJA h4

end CFSG.OddStandard.AltStdSec.SwapPartner
