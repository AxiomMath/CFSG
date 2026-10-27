module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64TwoA
public import CFSG.GH74.SectionalRankExtension
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Quot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec64_sectional_le_three [Finite G] {T H : Subgroup G} {F : Type} [Group F]
    (hQ : QuotEquivTo T (T ⊓ H) F) (hU : IsCyclic ↥(T ⊓ H))
    (hF : CFSG.GH74.SectionalTwoRankLE F 2) : CFSG.GH74.sectionalTwoRank T ≤ 3 := by
  obtain ⟨φ, hφ, hker⟩ := hQ
  haveI : Finite ↥T := inferInstance
  haveI : φ.ker.Normal := MonoidHom.normal_ker φ
  rw [CFSG.GH74.sectionalTwoRank_le_iff]
  have hcyc : CFSG.GH74.SectionalTwoRankLE ↥(φ.ker) 1 := by
    haveI : IsCyclic ↥(T ⊓ H) := hU
    have hle : T ⊓ H ≤ T := inf_le_left
    rw [hker]
    exact CFSG.GH74.SectionalTwoRankLE.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hle).symm
      (CFSG.GH74.SectionalTwoRankLE.of_isCyclic inferInstance)
  have hquot : CFSG.GH74.SectionalTwoRankLE (↥T ⧸ φ.ker) 2 :=
    CFSG.GH74.SectionalTwoRankLE.of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm hF
  exact (CFSG.GH74.SectionalTwoRankLE.of_normal φ.ker hcyc hquot).mono (by norm_num)

theorem sec64_case_eq [Finite G] {T H : Subgroup G} {x y : G} (c : Sec64Cfg T H x y)
    (halt : Sec64Tri T H y) (hTR : T ≤ centralizer ({y} : Set G)) : Sec64Out T H y := by
  have hT : T ⊓ centralizer ({y} : Set G) = T := inf_eq_left.mpr hTR
  have hU : IsCyclic ↥(T ⊓ H) := by
    have h := c.hU
    rwa [hT] at h
  unfold Sec64Tri at halt
  rw [hT] at halt
  unfold Sec64Out
  rw [hT]
  rcases halt with h | ⟨-, hQ⟩ | hQ
  · left
    have hne : x ≠ y := fun hxy => c.hxH (hxy ▸ c.hyH)
    refine le_antisymm ?_ (sec64_two_le_pRank c.hx c.hy c.hxy hne c.hxT c.hyT)
    exact CFSG.SectionRank.pRank_le (p := 2) (k := 2) (by norm_num)
      (fun E hET hE => by simpa using sec63_elem_le_of_relIndex hU h E hET hE)
  · right
    refine ⟨sec64_not_relIndex_le_two hQ ?_, ?_⟩
    · rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    · refine sec64_sectional_le_three hQ hU ?_
      have h2 : CFSG.GH74.SectionalTwoRankLE (Multiplicative (ZMod 2)) 1 :=
        CFSG.GH74.SectionalTwoRankLE.of_isCyclic inferInstance
      simpa using CFSG.GH74.SectionalTwoRankLE.prod h2 h2
  · right
    refine ⟨sec64_not_relIndex_le_two hQ ?_, ?_⟩
    · rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    · exact sec64_sectional_le_three hQ hU
        ((CFSG.GH74.SectionalTwoRankLE.of_isCyclic
          (inferInstance : IsCyclic (Multiplicative (ZMod 4)))).mono (by norm_num))

end CFSG.OddStandard.SmallF3.Omega
