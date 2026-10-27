module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3OutCore
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.OuterAutomorphisms

theorem threeFilter_projectiveSL_three (k : Type) [Field k] [Finite k] :
    ThreeFilter (inner (LinearFlag.projectiveSL 3 k)) := by
  obtain ⟨hR, -⟩ := LinearFlag.automorphism_generation (K := k) (n := 3) le_rfl
  obtain ⟨hID, -, hDnorm, hEnorm, -, ⟨g, -, hg⟩, -, hindex, -, -⟩ :=
    LinearFlag.standard_outer_quotients (n := 3) (K := k)
  rw [hR] at hDnorm hEnorm hindex
  have hDn : (LinearFlag.linearAutGroup 3 k).Normal :=
    ⟨fun d hd g => hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨g, Subgroup.mem_top g⟩⟩
  have hEn : (LinearFlag.semilinearAutGroup 3 k).Normal :=
    ⟨fun d hd g => hEnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨g, Subgroup.mem_top g⟩⟩
  have hindex' : (LinearFlag.semilinearAutGroup 3 k).index ≤ 2 := by
    rwa [← Subgroup.relIndex_top_right]
  have hcop : ∀ j : ℕ, Nat.Coprime (3 ^ j) (LinearFlag.semilinearAutGroup 3 k).index := by
    intro j
    have hpos : (LinearFlag.semilinearAutGroup 3 k).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (by omega : (LinearFlag.semilinearAutGroup 3 k).index = 1 ∨
        (LinearFlag.semilinearAutGroup 3 k).index = 2) with h | h <;> rw [h]
    · exact Nat.coprime_one_right _
    · exact Nat.Coprime.pow_left _ (by norm_num)
  refine ⟨LinearFlag.linearAutGroup 3 k, LinearFlag.semilinearAutGroup 3 k, hDn, hID,
    LinearFlag.linearAutGroup_le_semilinearAutGroup, fun d hd => ⟨1, ?_⟩,
    commutator_mem_of_cyclic_quotient hg, fun a j ha => mem_of_pow_mem_of_coprime_index (hcop j) ha⟩
  have hdvd := UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := k) (n := 3) (by norm_num)
  rw [pow_one]
  exact pow_mem_normal_of_relIndex_dvd (hdvd.trans (Nat.gcd_dvd_left 3 _)) hd

end CFSG.LocalAnalysis.RankThreeTheoremC
