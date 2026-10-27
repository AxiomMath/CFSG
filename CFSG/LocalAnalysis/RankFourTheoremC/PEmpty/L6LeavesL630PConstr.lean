module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630NineD

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

theorem pConstrainedFivePart_holds : PConstrainedFivePart := by
  intro G _ _ M P z hz hPM hzP hcomm hPC
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPtop : CFSG.ABGLocalTools.IsSylowOf 5 (P : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  have hPM' : CFSG.ABGLocalTools.IsSylowOf 5 (P : Subgroup G) M :=
    hPtop.of_le hPM le_top
  have hTM : (⊤ : Subgroup M).map M.subtype = M := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hPsub : ((P : Subgroup G).subgroupOf M).map M.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPM]
  have hPM'' : CFSG.ABGLocalTools.IsSylowOf 5 ((P : Subgroup G).subgroupOf M) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff M, hTM, hPsub]
    exact hPM'
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 5
      ((P : Subgroup G).subgroupOf M ⊓ CFSG.Op_p'p 5 ↥M) (CFSG.Op_p'p 5 ↥M) :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hPM'' le_top
      (le_of_eq (Subgroup.normalizer_eq_top _).symm)
  have hzc : (⟨z, hz⟩ : ↥M) ∈ Subgroup.centralizer
      (((P : Subgroup G).subgroupOf M ⊓ CFSG.Op_p'p 5 ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhP : (h : G) ∈ (P : Subgroup G) :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hh).1
    apply Subtype.ext
    exact hcomm _ hhP
  exact hPC _ hsyl hzc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
