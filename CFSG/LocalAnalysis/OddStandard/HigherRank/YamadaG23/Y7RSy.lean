module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RCh
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RCo
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {t : G} {P U : Subgroup G}

theorem Wr7.isPGroup_star (h : Wr7 t P U) (hP : IsPGroup 2 P) : IsPGroup 2 (wrStar t P) := by
  have ht : IsPGroup 2 (zpowers t) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_of_pow_eq_one h.t_sq
  change IsPGroup 2 ↥(P ⊔ zpowers t)
  exact hP.to_sup_of_normal_left' ht
    ((le_sup_right : zpowers t ≤ P ⊔ zpowers t).trans h.le_normalizer_star)

theorem Wr7.isSylowIn_star (h : Wr7 t P U) (hU : RankFacts U) (htP : t ∉ P)
    (hP : IsPGroup 2 P) {T : Subgroup G}
    (hT : IsSylowIn 2 (centralizer ({t} : Set G)) T)
    (hTe : T = wrStar t P ⊓ centralizer ({t} : Set G)) : IsSylowIn 2 ⊤ (wrStar t P) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ0p : IsPGroup 2 (wrStar t P) := Wr7.isPGroup_star h hP
  obtain ⟨Q, hQ0Q⟩ := hQ0p.exists_le_sylow
  have hQ0eqQ : wrStar t P = Q := by
    by_contra hne
    have hHtop : (wrStar t P).subgroupOf (Q : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      exact hne (le_antisymm hQ0Q (Subgroup.subgroupOf_eq_top.mp htop))
    have hnc : NormalizerCondition ↥Q := by
      haveI : Group.IsNilpotent ↥Q := Q.isPGroup'.isNilpotent
      exact Group.normalizerCondition_of_isNilpotent
    have hHnorm : (wrStar t P).subgroupOf (Q : Subgroup G) <
        normalizer ((wrStar t P).subgroupOf (Q : Subgroup G)) := hnc _ hHtop
    obtain ⟨y, hyn, hyH⟩ := SetLike.not_le_iff_exists.mp (not_le_of_gt hHnorm)
    let x : G := (y : G)
    have hyQ : x ∈ Q := y.2
    have hxN : x ∈ normalizer ((wrStar t P : Subgroup G) : Set G) := by
      have hy' : y ∈ (normalizer (wrStar t P)).subgroupOf (Q : Subgroup G) := by
        rw [Subgroup.subgroupOf_normalizer_eq hQ0Q]
        exact hyn
      exact Subgroup.mem_subgroupOf.mp hy'
    have hxP : x ∈ normalizer (P : Set G) := Wr7.normalizer_star_le h hU x hxN
    have htQ0 : t ∈ wrStar t P := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have hxtQ0 : x * t * x⁻¹ ∈ wrStar t P :=
      (Subgroup.mem_normalizer_iff.mp hxN t).mp htQ0
    have hxtP : x * t * x⁻¹ ∉ P := fun hmem =>
      htP ((Subgroup.mem_normalizer_iff.mp hxP t).mpr hmem)
    have hc : (x * t * x⁻¹) * t⁻¹ ∈ P := by
      rcases (Wr7.mem_star (h := h)).mp hxtQ0 with hmem | hmem
      · exact absurd hmem hxtP
      · exact hmem
    have hc' : (x⁻¹)⁻¹ * (t * x⁻¹ * t⁻¹) ∈ P := by
      simpa only [inv_inv, mul_assoc] using hc
    obtain ⟨p, hpP, hpc⟩ := Wr7.exists_fixed h hc'
    have hpQ0 : p ∈ wrStar t P := Subgroup.mem_sup_left hpP
    have hzcent : x⁻¹ * p ∈ centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hpc).symm
    have hzQ : x⁻¹ * p ∈ Q :=
      (Q : Subgroup G).mul_mem ((Q : Subgroup G).inv_mem hyQ) (hQ0Q hpQ0)
    have hz : x⁻¹ * p ∈ (Q : Subgroup G) ⊓ centralizer ({t} : Set G) := ⟨hzQ, hzcent⟩
    have hQ2 : IsPGroup 2 ↥((Q : Subgroup G) ⊓ centralizer ({t} : Set G)) :=
      Q.isPGroup'.to_le inf_le_left
    have hTle : T ≤ (Q : Subgroup G) ⊓ centralizer ({t} : Set G) := by
      rw [hTe]
      exact inf_le_inf_right _ hQ0Q
    have hTeq : T = (Q : Subgroup G) ⊓ centralizer ({t} : Set G) :=
      sylowIn_eq_of_le hT hQ2 inf_le_right hTle
    have hzT : x⁻¹ * p ∈ T := by
      rw [hTeq]
      exact hz
    have hzQ0 : x⁻¹ * p ∈ wrStar t P := by
      rw [hTe] at hzT
      exact hzT.1
    have hxinv : x⁻¹ ∈ wrStar t P := by
      have hxinv' : x⁻¹ = (x⁻¹ * p) * p⁻¹ := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [hxinv']
      exact (wrStar t P).mul_mem hzQ0 ((wrStar t P).inv_mem hpQ0)
    have hxQ0 : x ∈ wrStar t P := by
      simpa using (wrStar t P).inv_mem hxinv
    have hxQ0' : x ∉ wrStar t P := fun hx =>
      hyH (Subgroup.mem_subgroupOf.mpr hx)
    exact hxQ0' hxQ0
  refine ⟨le_top, hQ0p, ?_⟩
  rw [Subgroup.relIndex_top_right, hQ0eqQ]
  exact Q.not_dvd_index

end CFSG.OddStandard.HigherRank.YamadaG23
