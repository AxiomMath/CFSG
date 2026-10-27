module

public import CFSG.ClassicalInvolution.Asc77.AscC25J14

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Quot

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]


theorem exists_conj_omegaStarNbr_gen (hΩ : HypOmegaGen Ω) (hΩ' : HypOmegaGen (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaStarNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ n ∈ N, J ∈ omegaStarNbr Ω (conjSub n K) := by
  exact E187C.exists_conj_omegaStarNbr_of (fun hJ hUb hUbJ => exists_lift_USet_gen hΩ' hN hJ hUb hUbJ)
    (fun hU => Sec6Gen.isPGroup_of_mem_USet hΩ hU) (fun hK hU2 hUN => exists_conj_normalizer_gen hΩ hN hK hU2 hUN) hK hJ h

theorem aEmpty_quotFamily_gen (hΩ : HypOmegaGen Ω) (hΩ' : HypOmegaGen (quotFamily Ω N))
    (hN : Odd (Nat.card N)) (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M := by
  exact E187C.aEmpty_quotFamily_of hΩ.conjInvariant
    (fun hK hJ h => exists_conj_omegaStarNbr_gen hΩ hΩ' hN hK hJ h)
    (fun hK hT hTJ => Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hT hTJ)
    (fun hK => Sec6Gen.exists_uniqueInvolution hΩ hK) hN hA

end Quot

end CFSG.ClassicalInvolution.Asc77.C25J
