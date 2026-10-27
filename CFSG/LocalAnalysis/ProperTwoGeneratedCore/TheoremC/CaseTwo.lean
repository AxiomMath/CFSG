module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.CaseTwoBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Statement

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

namespace CoreConfig

variable {Y : Subgroup X} {u z : X} (hc : CoreConfig Y u z)

section HighRank

variable {J : Subgroup X} (hJ : CFSG.IsComponent J) (hrank : 2 ≤ CFSG.Open.pRank 2 J)
include hc hJ hrank

theorem highRank_characteristic : J.Characteristic := by
  obtain ⟨P, hPY, hcore, -, -⟩ := hc.sylow
  exact proper_full_core_high_rank_component_characteristic P Y hc.ne_top hPY hcore J
    ((CFSG.isComponent_iff_open J).mp hJ) hrank

theorem highRank_normal : J.Normal := by
  have := hc.highRank_characteristic hJ hrank
  infer_instance

theorem highRank_not_le : ¬ J ≤ Y := by
  obtain ⟨P, hPY, hcore, -, -⟩ := hc.sylow
  have := hc.highRank_normal hJ hrank
  exact normal_rank_two_not_le_overgroup P Y hc.ne_top hPY hcore J hrank

theorem highRank_eq_of_mem_centralizer {k : X} (hk : k ∈ Subgroup.centralizer (J : Set X))
    (hk2 : orderOf k = 2) : k = u := by
  obtain ⟨P, hPY, hcore, -, -⟩ := hc.sylow
  have := hc.highRank_normal hJ hrank
  have hle := normal_rank_two_centralizer_rank_le_one P Y hc.ne_top hPY hcore J hrank
  have hu : u ∈ Subgroup.centralizer (J : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun y _ => (hc.commute_center y).eq
  by_contra hne
  have h := two_le_pRank_of_commuting_involutions hk hu hk2 hc.order hne (hc.commute_center k)
  omega

end HighRank

section Lever

variable {P : Sylow 2 X} (hPY : (P : Subgroup X) ≤ Y) {y : X} (hy : orderOf y = 2)
  (hyP : y ∈ (P : Subgroup X)) (hyc : y ∈ Subgroup.centralizer ((P : Subgroup X) : Set X))
  (hyne : y ≠ u)
include hc hPY hy hyP hyc hyne

theorem highRank_dichotomy {J : Subgroup X} (hJ : CFSG.IsComponent J) (huJ : u ∈ J)
    (hrank : 2 ≤ CFSG.Open.pRank 2 J) :
    (y ∈ J ∧ y ∉ (Subgroup.center J).map J.subtype) ∨
      (y ∉ J ∧ ∃ k ∈ J ⊓ Y, ∃ t ∈ (P : Subgroup X) ⊓ J,
        t ∉ (Subgroup.center J).map J.subtype ∧ orderOf t = 2 ∧ Commute y t ∧
          k⁻¹ * y * k = y * t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ2, hZO⟩ := component_center_le_twoCore hc.oddCore_eq_bot hJ
  have hO2P : CFSG.pCore 2 X ≤ (P : Subgroup X) := CFSG.pCore_isPGroup.le_sylow_of_normal P
  by_cases hyJ : y ∈ J
  · refine Or.inl ⟨hyJ, fun hyZ => hyne ?_⟩
    have hyO := hZO hyZ
    exact hc.caseTwo_eq_of_mem_twoCore hyO hy
  refine Or.inr ⟨hyJ, ?_⟩
  rcases zStarStep ((CFSG.isComponent_iff_open J).mp hJ).2.2
      (even_card_of_orderOf_eq_two huJ hc.order) hy
      (mem_normalizer_component hc.oddCore_eq_bot P hyc hJ) inf_le_right
      (P.isPGroup'.to_le inf_le_left)
      (fun _ hRJ hR => card_le_card_sylow_inf_of_isSubnormal P hJ.2 hRJ hR)
      (fun q hq => (Subgroup.mem_centralizer_iff.mp hyc q hq.1).symm) (Subgroup.map_subtype_le _)
      (by
        rintro _ ⟨c, hc', rfl⟩
        exact Subgroup.mem_centralizer_iff.mpr fun j hj =>
          congrArg Subtype.val (Subgroup.mem_center_iff.mp hc' ⟨j, hj⟩))
      (fun c hc' => (Subgroup.mem_centralizer_iff.mp hyc c (hO2P (hZO hc'))).symm)
      (hZ2.map J.subtype) with h | h
  · exact absurd (hc.highRank_eq_of_mem_centralizer hJ hrank
      (Subgroup.mem_centralizer_iff.mpr fun j hj => (h j hj).eq.symm) hy) hyne
  · obtain ⟨k, hk, t, htQ, htC, htt, hkt⟩ := h
    have ht2 : orderOf t = 2 :=
      orderOf_eq_two_of_mul_self htt fun h1 => htC (h1 ▸ Subgroup.one_mem _)
    have hkY : k ∈ Y := hc.mem_of_conj_mem (hPY hyP) hy hyne
      (by rw [hkt]; exact Y.mul_mem (hPY hyP) (hPY htQ.1))
    exact ⟨k, ⟨hk, hkY⟩, t, htQ, htC, ht2,
      (Subgroup.mem_centralizer_iff.mp hyc t htQ.1).symm, hkt⟩

theorem highRank_lever {J : Subgroup X} (hJ : CFSG.IsComponent J) (huJ : u ∈ J)
    (hrank : 2 ≤ CFSG.Open.pRank 2 J) :
    y ∈ J ∨ (y ∉ J ∧ ∃ k ∈ J ⊓ Y, ∃ t ∈ (P : Subgroup X) ⊓ J, orderOf t = 2 ∧
      (∃ c ∈ J, ¬ Commute c t) ∧ k⁻¹ * y * k = y * t) := by
  rcases hc.highRank_dichotomy hPY hy hyP hyc hyne hJ huJ hrank with ⟨hyJ, -⟩ | ⟨hyJ, h⟩
  · exact Or.inl hyJ
  obtain ⟨k, hk, t, htQ, htZ, ht2, -, hkt⟩ := h
  refine Or.inr ⟨hyJ, k, hk, t, htQ, ht2, ?_, hkt⟩
  by_contra hall
  push Not at hall
  exact htZ ⟨⟨t, htQ.2⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hall g g.2).eq, rfl⟩

end Lever

end CoreConfig

theorem caseTwoReduction : CaseTwoReduction := by
  intro X _ _ Y u z hc hcase
  obtain ⟨P, hPY, hcore, hzP, hzc⟩ := hc.sylow
  obtain ⟨J, hJ, hrank⟩ := hc.caseTwo_exists_two_le_pRank hcase
  exact ⟨P, J, hPY, hcore, hzP, hzc, hJ, hc.highRank_normal hJ hrank, hcase J hJ, hrank,
    hc.highRank_not_le hJ hrank, hc.highRank_lever hPY hc.lever_order hzP
      (CoreConfig.caseTwo_lever_mem_centralizer hzc) hc.lever_ne hJ (hcase J hJ) hrank⟩

end CFSG.ProperTwoGeneratedCore.TheoremC
