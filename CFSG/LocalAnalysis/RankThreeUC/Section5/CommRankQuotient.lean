module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CommRankDef
public import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

theorem commRank_eq_fixedQuot_finrank {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (t : G) :
    commRank ρ t = Module.finrank (ZMod 2) (V ⧸ fixedSubmodule ρ (Subgroup.zpowers t)) := by
  have hker : fixedSubmodule ρ (Subgroup.zpowers t) = LinearMap.ker (ρ t - 1) := by
    ext v
    simp only [fixedSubmodule, Representation.mem_invariants, LinearMap.mem_ker,
      LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · intro h
      exact h ⟨t, Subgroup.mem_zpowers t⟩
    · intro h ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hi : ρ t⁻¹ v = v := by
        calc ρ t⁻¹ v = ρ t⁻¹ (ρ t v) := by rw [h]
          _ = v := by
            have := congrArg (fun f => f v) (map_mul ρ t⁻¹ t)
            simpa using this.symm
      show ρ (t ^ k) v = v
      induction k using Int.induction_on with
      | zero => simp
      | succ n ih =>
        rw [zpow_add_one, map_mul]
        simp only [Module.End.mul_apply, h]
        exact ih (by simp)
      | pred n ih =>
        rw [zpow_sub_one, map_mul]
        simp only [Module.End.mul_apply, map_inv, hi]
        exact ih (by simp)
  unfold commRank
  rw [hker]
  exact (LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange (ρ t - 1))).symm

end Section5

end CFSG.LocalAnalysis.RankThreeUC
