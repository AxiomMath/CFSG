module

public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open Subgroup

private theorem mem_zpowers_of_orderOf_three_of_isCyclic {X : Type} [Group X] [Finite X]
    (H : Subgroup X) [IsCyclic H] {b s : X} (hbH : b ∈ H) (hsH : s ∈ H)
    (hb : orderOf b = 3) (hs : orderOf s = 3) : s ∈ Subgroup.zpowers b := by
  have hEq : Subgroup.zpowers (⟨s, hsH⟩ : H) = Subgroup.zpowers (⟨b, hbH⟩ : H) :=
    IsCyclic.subgroup_eq_iff_card_eq.2 (by simp [Nat.card_zpowers, Subgroup.orderOf_mk, hs, hb])
  have hmem : (⟨s, hsH⟩ : H) ∈ Subgroup.zpowers (⟨b, hbH⟩ : H) := by
    rw [← hEq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hbk : b ^ k = s := by simpa using congrArg Subtype.val hk
  rw [← hbk]
  exact Subgroup.zpow_mem_zpowers b k

theorem exists_conj_mem_zpowers_of_pRank_le_one {X : Type} [Group X] [Finite X]
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1) (a b : X)
    (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ g : X, g * a * g⁻¹ ∈ Subgroup.zpowers b := by
  haveI : Finite (Sylow 3 X) :=
    Finite.of_injective (fun P : Sylow 3 X => (P : Set X)) SetLike.coe_injective
  have hA : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, ha])
  have hB : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, hb])
  obtain ⟨Pa, hPa⟩ := hA.exists_le_sylow
  obtain ⟨Pb, hPb⟩ := hB.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Pb Pa
  have hrkPb : CFSG.pRank 3 (Pb : Subgroup X) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top).trans hrk
  have hcyc : IsCyclic (Pb : Subgroup X) := by
    rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification
      Nat.prime_three Pb.isPGroup').mp hrkPb with h | ⟨h, -⟩
    · exact h
    · norm_num at h
  have haPa : a ∈ (Pa : Subgroup X) := hPa (Subgroup.mem_zpowers a)
  rw [← hg, Sylow.coe_subgroup_smul] at haPa
  obtain ⟨s, hsPb, hsa⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp haPa
  have hsa' : g * s * g⁻¹ = a := hsa
  have hconj : SemiconjBy g s a := by
    show g * s = a * g
    rw [← hsa']
    group
  have hsord : orderOf s = 3 := (SemiconjBy.orderOf_eq g hconj).trans ha
  have hbPb : b ∈ (Pb : Subgroup X) := hPb (Subgroup.mem_zpowers b)
  have hsb : s ∈ Subgroup.zpowers b :=
    mem_zpowers_of_orderOf_three_of_isCyclic (Pb : Subgroup X) hbPb hsPb hb hsord
  refine ⟨g⁻¹, ?_⟩
  have hfin : g⁻¹ * a * g⁻¹⁻¹ = s := by
    rw [← hsa']
    group
  rw [hfin]
  exact hsb

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
