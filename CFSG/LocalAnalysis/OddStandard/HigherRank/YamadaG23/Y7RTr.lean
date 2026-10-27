module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RSy
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RHb
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RNc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.ExtremalTransfer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {t : G} {P U : Subgroup G}

theorem Wr7.transfer_data (h : Wr7 t P U) {S T : Subgroup G} (hS : RankFacts S)
    (hS2 : IsPGroup 2 S) (hc : P ⊓ centralizer ({t} : Set G) = S) (htP : t ∉ P)
    (hcomm : ∀ x ∈ S, x * t = t * x) (hTS : T = S ⊔ zpowers t)
    (hT : IsSylowIn 2 (centralizer ({t} : Set G)) T) :
    ∃ Q N : Subgroup G, IsSylowIn 2 ⊤ Q ∧ N ≤ Q ∧
      SecProp Q N (fun Y _ _ _ => IsCyclic Y) ∧ ∀ x : G, IsExtremalConj Q t x → x ∉ N := by
  classical
  have hU : RankFacts U := Wr7.rankFacts_left h hc hS
  have hP : IsPGroup 2 P := Wr7.isPGroup h hc hS2
  have hTe : T = wrStar t P ⊓ centralizer ({t} : Set G) := by
    rw [hTS, ← hc, Wr7.centEl_star h]
  have hQ : IsSylowIn 2 ⊤ (wrStar t P) := Wr7.isSylowIn_star h hU htP hP hT hTe
  have hb : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → IsElemAbelian 2 E →
      Nat.card E ≤ 16 := cent_elem_bound hS h.t_sq hTS hcomm hT
  refine ⟨wrStar t P, P, hQ, le_sup_left, ?_, ?_⟩
  ·
    have hnorm : (P.subgroupOf (wrStar t P)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (Wr7.le_normalizer_star h)
    haveI : (P.subgroupOf (wrStar t P)).Normal := hnorm
    refine ⟨hnorm, ?_⟩
    let N : Subgroup ↥(wrStar t P) := P.subgroupOf (wrStar t P)
    haveI : N.Normal := hnorm
    have htQ : t ∈ wrStar t P := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    let g : ↥(wrStar t P) ⧸ N := QuotientGroup.mk' N ⟨t, htQ⟩
    refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, ?_⟩
    refine (Subgroup.eq_top_iff' _).mpr ?_
    intro y
    refine QuotientGroup.induction_on y ?_
    intro x
    change QuotientGroup.mk' N x ∈ Subgroup.zpowers g
    rcases (Wr7.mem_star h).mp x.2 with hxP | hxPt
    · have hxN : x ∈ N := Subgroup.mem_subgroupOf.mpr hxP
      have h1 : QuotientGroup.mk' N x = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hxN
      rw [h1]
      exact Subgroup.one_mem _
    · let p : ↥(wrStar t P) := ⟨(x : G) * t⁻¹, Subgroup.mem_sup_left hxPt⟩
      let pt : ↥(wrStar t P) := ⟨t, htQ⟩
      have hpN : p ∈ N := by
        rw [Subgroup.mem_subgroupOf]
        exact hxPt
      have hp1 : QuotientGroup.mk' N p = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hpN
      have hx_eq : x = p * pt := by
        apply Subtype.ext
        simp only [p, pt, Subgroup.coe_mul, Subgroup.coe_mk]
        group
      have hmg : QuotientGroup.mk' N x = g := by
        calc QuotientGroup.mk' N x
            = QuotientGroup.mk' N (p * pt) := by rw [hx_eq]
          _ = QuotientGroup.mk' N p * QuotientGroup.mk' N pt := map_mul _ _ _
          _ = 1 * g := by rw [hp1]
          _ = g := one_mul g
      rw [hmg]
      exact Subgroup.mem_zpowers g
  · intro x hx hxP
    exact (Wr7.not_isConj h hU hb x hxP) hx.2.1

end CFSG.OddStandard.HigherRank.YamadaG23
