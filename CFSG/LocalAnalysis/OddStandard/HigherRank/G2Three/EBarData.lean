module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.EBarSub
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.EBarK
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.InductionSU43
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Lift

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup

theorem exists_ebar_data {E : Type} [Group E] [Finite E] {K : Subgroup E} {u : E}
    (hK : CFSG.IsQuasisimple ↥K) (huK : u ∈ K) (hcomm : ∀ k ∈ K, k * u = u * k)
    (hKn : (K.subgroupOf (centralizer ({u} : Set E))).Normal)
    (hu2 : u * u ∈ center E) (hu : u ∉ center E)
    (htwo : ∀ c ∈ K, (∀ k ∈ K, k * c = c * k) → IsPGroup 2 (zpowers c) → c ∈ zpowers u)
    (hB : IsSU43 (↥K ⧸ CFSG.oddCore ↥K)) :
    ∃ (t : E ⧸ center E) (J : Subgroup (E ⧸ center E)),
      orderOf t = 2 ∧ J ≤ centralizer ({t} : Set (E ⧸ center E)) ∧
      (J.subgroupOf (centralizer ({t} : Set (E ⧸ center E)))).IsSubnormal ∧ t ∈ J ∧
      CFSG.IsQuasisimple ↥J ∧ CFSG.ComponentClassification.HarrisLit.IsTwoQuasisimple ↥J ∧
      CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSU 4 3 1 ∧
      (∀ x ∈ center ↥J, orderOf x ≠ 4) ∧
      Nonempty (↥K ⧸ CFSG.Open.fusionZStar ↥K ≃* ↥J ⧸ CFSG.Open.fusionZStar ↥J) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : E →* E ⧸ center E := QuotientGroup.mk' (center E)
  let t : E ⧸ center E := π u
  let J : Subgroup (E ⧸ center E) := K.map π
  have ht2 : t ^ 2 = 1 := by
    show π u ^ 2 = 1
    rw [pow_two, ← map_mul]
    exact (QuotientGroup.eq_one_iff (N := center E) (u * u)).mpr hu2
  have ht1 : t ≠ 1 := by
    intro h
    exact hu ((QuotientGroup.eq_one_iff (N := center E) u).mp h)
  have horder : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hKle : K ≤ centralizer ({u} : Set E) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm k hk)
  have hJcent : J ≤ centralizer ({t} : Set (E ⧸ center E)) := by
    intro k hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    show π k' * π u = π u * π k'
    rw [← map_mul, ← map_mul, hcomm k' hk']
  have hsub : (J.subgroupOf (centralizer ({t} : Set (E ⧸ center E)))).IsSubnormal := by
    simpa only [J, t, π] using subnormal_map_center_centralizer u K hKle hKn
  have htJ : t ∈ J := Subgroup.mem_map_of_mem π huK
  have hJq : CFSG.IsQuasisimple ↥J := by
    simpa only [J, π] using isQuasisimple_map_mk_center (K := K) hK
  have h2J : 2 ∣ Nat.card ↥J := by
    rw [← horder]
    exact J.orderOf_dvd_natCard htJ
  have h2K : 2 ∣ Nat.card ↥K :=
    dvd_trans h2J (Subgroup.card_map_dvd (H := K) π)
  have hTwoQ : CFSG.ComponentClassification.HarrisLit.IsTwoQuasisimple ↥J :=
    (CFSG.ComponentClassification.HarrisLit.P1.isTwoQuasisimple_of_isQuasisimple hJq h2J).1
  have hLie : CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSU 4 3 1 := by
    have hLieK : CFSG.Blueprint.LieModel (↥K ⧸ center ↥K) .PSU 4 3 1 :=
      lieModel_quotient_center_of_isSU43 hK hB
    obtain ⟨e⟩ := nonempty_quotient_center_equiv_map (K := K) hK
    exact CFSG.ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv
      (by simpa only [J, π] using e) hLieK
  have hZ4 : ∀ x ∈ center ↥J, orderOf x ≠ 4 := fun x hx =>
    not_orderOf_four_of_mem_center_map (K := K) hK hu2 htwo x hx
  have hfusion : Nonempty (↥K ⧸ CFSG.Open.fusionZStar ↥K ≃*
      ↥J ⧸ CFSG.Open.fusionZStar ↥J) := by
    simpa only [J, π] using
      nonempty_fusionZStar_equiv_map_mk_center (K := K) hK h2K h2J
  exact ⟨t, J, horder, hJcent, hsub, htJ, hJq, hTwoQ, hLie, hZ4, hfusion⟩

end CFSG.OddStandard.HigherRank.G2Three
