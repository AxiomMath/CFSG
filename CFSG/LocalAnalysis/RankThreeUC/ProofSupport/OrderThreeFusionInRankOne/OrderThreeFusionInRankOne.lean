module

public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OrderThreeFusionInRankOne

open Subgroup Pointwise

theorem exists_conj_of_card_three {G : Type} [Group G] [Finite G] {K D E : Subgroup G}
    (hK : CFSG.Open.pRank 3 K ≤ 1) (hDK : D ≤ K) (hEK : E ≤ K) (hD : Nat.card D = 3)
    (hE : Nat.card E = 3) :
    ∃ k ∈ K, E = D.map (MulAut.conj k).toMonoidHom := by
  have exists_conj_of_card_prime {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
      (hp2 : p ≠ 2) {K D E : Subgroup G} (hK : CFSG.Open.pRank p K ≤ 1) (hDK : D ≤ K)
      (hEK : E ≤ K) (hD : Nat.card D = p) (hE : Nat.card E = p) :
      ∃ k ∈ K, E = D.map (MulAut.conj k).toMonoidHom := by
    have hKr : CFSG.pRank p K ≤ 1 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]; exact hK
    have hDc : Nat.card (D.subgroupOf K) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv]; exact hD
    have hEc : Nat.card (E.subgroupOf K) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv]; exact hE
    haveI : Fact p.Prime := ⟨hp⟩
    have hDp : IsPGroup p (D.subgroupOf K) := IsPGroup.of_card (n := 1) (by rw [hDc]; simp)
    have hEp : IsPGroup p (E.subgroupOf K) := IsPGroup.of_card (n := 1) (by rw [hEc]; simp)
    obtain ⟨P, hDP⟩ := hDp.exists_le_sylow
    obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P Q
    have hcyc : IsCyclic (Q : Subgroup K) :=
      CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_sylow_of_pRank_le_one hp hp2 hKr Q
    have hmap : ∀ S : Subgroup K, MulAut.conj k • S = S.map (MulAut.conj k).toMonoidHom := by
      intro S; exact Subgroup.pointwise_smul_def S
    have hle : (D.subgroupOf K).map (MulAut.conj k).toMonoidHom ≤ (Q : Subgroup K) := by
      rw [← hmap, ← hk, Sylow.coe_subgroup_smul]
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hDP
    have hcard : Nat.card ((D.subgroupOf K).map (MulAut.conj k).toMonoidHom) = p := by
      rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hDc]
    have heq : (D.subgroupOf K).map (MulAut.conj k).toMonoidHom = E.subgroupOf K := by
      set A := (D.subgroupOf K).map (MulAut.conj k).toMonoidHom with hA
      have hAQ := hle
      have hEQ' := hEQ
      have hca : Nat.card (A.subgroupOf (Q : Subgroup K)) = p := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv]; exact hcard
      have hcb : Nat.card ((E.subgroupOf K).subgroupOf (Q : Subgroup K)) = p := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ').toEquiv]; exact hEc
      have h1 := (IsCyclic.subgroup_eq_iff_card_eq (H := A.subgroupOf (Q : Subgroup K))
        (K := (E.subgroupOf K).subgroupOf (Q : Subgroup K))).2 (by rw [hca, hcb])
      have h2 := congrArg (Subgroup.map (Q : Subgroup K).subtype) h1
      rwa [Subgroup.map_subgroupOf_eq_of_le hAQ, Subgroup.map_subgroupOf_eq_of_le hEQ'] at h2
    have h3 := congrArg (Subgroup.map K.subtype) heq
    refine ⟨k, k.2, ?_⟩
    rw [Subgroup.map_subgroupOf_eq_of_le hEK] at h3
    rw [← h3, Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_subgroupOf_eq_of_le hDK, Subgroup.map_map]
    congr 1
  exact exists_conj_of_card_prime Nat.prime_three (by decide) hK hDK hEK hD hE

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OrderThreeFusionInRankOne
