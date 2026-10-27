module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchMain
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitPair

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

theorem false_of_branch
    [Finite G] {ε : Eps} {t : G} {Q TH : Subgroup G}
    {ψ : V6 → G} (hB : NSplit.Branch ε t Q TH ψ) (hGt : ∀ K : Subgroup G, K.index = 2 → t ∈ K) :
    False := by
  obtain ⟨S, hS⟩ := hB.sylowModel
  exact false_of_sylowModel hB.orderOf_t hB.TH_le hB.TH_pgroup hB.TH_max hS hGt

theorem false_of_branch_of_simple
    [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {ε : Eps} {t : G} {Q TH : Subgroup G} {ψ : V6 → G}
    (hB : NSplit.Branch ε t Q TH ψ) : False :=
  false_of_branch hB fun K hK => (not_index_two hG hnab K hK).elim

end CFSG.EvenSmallLie.OmegaEight.SpBranch
