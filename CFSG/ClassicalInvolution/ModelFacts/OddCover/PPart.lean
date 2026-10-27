module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open scoped commutatorElement

variable {E X : Type*} [Group E] [Group X] {p : ℕ} [Fact p.Prime]

theorem ker_eq_bot_of_commutator_inf_eq_bot [Finite E] [Group.IsPerfect E] (π : E →* X)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hK : IsPGroup p π.ker)
    {U : Subgroup X} (hU : IsPGroup p U) (hUi : ¬ p ∣ U.index)
    (hcomm : ⁅U.comap π, U.comap π⁆ ⊓ π.ker = ⊥) : π.ker = ⊥ := by
  have hUp : IsPGroup p (U.comap π) := hU.comap_of_ker_isPGroup π hK
  have hindex : ¬ p ∣ (U.comap π).index := by
    rw [Subgroup.index_comap_of_surjective _ hπ]
    exact hUi
  let P : Sylow p E := hUp.toSylow hindex
  have hle := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P π.ker hcen hK
  have hP : (P : Subgroup E) = U.comap π := rfl
  rw [hP, Subgroup.map_subtype_commutator] at hle
  rw [eq_bot_iff, ← hcomm]
  exact le_inf hle le_rfl

end CFSG.ClassicalInvolution.ModelFacts.OddCover
