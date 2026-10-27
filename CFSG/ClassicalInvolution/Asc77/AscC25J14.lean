module

public import CFSG.ClassicalInvolution.Asc77.AscC25H1
public import CFSG.ClassicalInvolution.Asc77.AscC25I8
public import CFSG.ClassicalInvolution.Asc77.AscR10G2R

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


theorem exists_conj_normalizer_gen (hΩ : HypOmegaGen Ω) (hN : Odd (Nat.card N)) {K : Subgroup G}
    (hK : K ∈ Ω) {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUN : ∀ u ∈ U, QuotientGroup.mk' N u ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) :
    ∃ n ∈ N, U ≤ Subgroup.normalizer ((conjSub n K : Subgroup G) : Set G) := by
  exact E187C.exists_conj_normalizer_of hΩ.conjInvariant (fun hK hL h => exists_conj_of_map_eq_gen hΩ hN hK hL h) hN hK hU2 hUN

theorem exists_lift_USet_gen (hΩ' : HypOmegaGen (quotFamily Ω N)) (hN : Odd (Nat.card N))
    {J : Subgroup G} (hJ : J ∈ Ω) {Ub : Subgroup (G ⧸ N)} (hUb : Ub ∈ USet (quotFamily Ω N))
    (hUbJ : Ub ≤ J.map (QuotientGroup.mk' N)) :
    ∃ U ∈ USet Ω, U ≤ J ∧ U.map (QuotientGroup.mk' N) = Ub := by
  exact E187C.exists_lift_USet_of (fun hU => Sec6Gen.exists_data_of_mem_USet hΩ' hU)
    (fun hK hJ hA h4 hAK hAJ => Sec6Gen.eq_of_le_of_le hΩ' hK hJ hA h4 hAK hAJ) hN hJ hUb hUbJ

end Quot

end CFSG.ClassicalInvolution.Asc77.C25J
