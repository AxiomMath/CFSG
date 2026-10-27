module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G] [Finite G]

theorem pSubgroup_lt_normalizer_intersection
    (p : ℕ) (hp : p.Prime) (M Q : Subgroup G) (hQ : IsPGroup p Q) (hMQ : M < Q) :
    M < Q ⊓ Subgroup.normalizer (M : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsNilpotent Q := hQ.isNilpotent
  have hproper : M.subgroupOf Q < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro heq
    exact (not_le_of_gt hMQ) (Subgroup.subgroupOf_eq_top.mp heq)
  have hgrowth := Group.normalizerCondition_of_isNilpotent (G := Q) (M.subgroupOf Q) hproper
  have hmapgrowth := Subgroup.map_subtype_lt_map_subtype.mpr hgrowth
  rw [Subgroup.map_subgroupOf_eq_of_le hMQ.le] at hmapgrowth
  have hnormalizer : (Subgroup.normalizer (M.subgroupOf Q : Set Q)).map Q.subtype =
      Q ⊓ Subgroup.normalizer (M : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hMQ.le, Subgroup.subgroupOf_map_subtype, inf_comm]
  rwa [hnormalizer] at hmapgrowth

theorem odd_central_quotient_class_normalizes_specified_sylow
    (J : Subgroup G) [J.Normal] (hJodd : Odd (Nat.card J))
    (s : G) (hs : orderOf s = 2)
    (hcentral : QuotientGroup.mk' J s ∈ Subgroup.center (G ⧸ J))
    (p : ℕ) (hp : p.Prime) (R : Sylow p G) :
    ∃ r ∈ involutionPointClass s, r ∈ Subgroup.normalizer (R : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ProperTwoGeneratedCore.odd_central_quotient_invariant_sylow_exists
    p hp (⊤ : Subgroup G) J s hs hJodd le_top hcentral
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective
    (f := (⊤ : Subgroup G).subtype) (fun a => ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩) p R
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (⊤ : Subgroup G) P Q
  let r := (g : G) * s * (g : G)⁻¹
  have hn : r ∈ Subgroup.normalizer
      (((Q : Subgroup (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype : Subgroup G) : Set G) := by
    have hmap : ((P : Subgroup (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).map
        (MulAut.conj (g : G)).toMonoidHom =
      (Q : Subgroup (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      change _ = ((P : Subgroup (⊤ : Subgroup G)).map
        (MulAut.conj g).toMonoidHom).map (⊤ : Subgroup G).subtype
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    have hnorm := Subgroup.le_normalizer_map (MulAut.conj (g : G)).toMonoidHom
      (Subgroup.mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom hP)
    rw [hmap] at hnorm
    exact hnorm
  refine ⟨r, ⟨(g : G)⁻¹, by simp only [r, rightConjugateElem, inv_inv]⟩, ?_⟩
  have hQR : (Q : Subgroup (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype =
      (R : Subgroup G) := congrArg (fun T : Sylow p G => (T : Subgroup G)) hQ
  rwa [hQR] at hn

theorem two_le_of_modEq_two (p n : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hn : n ≡ 2 [MOD p]) : 2 ≤ n := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le
    (fun heq => by rw [← heq] at hodd; norm_num at hodd)
  by_contra hsmall
  have heq := hn.eq_of_lt_of_lt (by omega) hp2
  omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
