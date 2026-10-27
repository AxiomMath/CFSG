module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LargeExtraspecial.AS35LInvA
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LargeExtraspecial.Asc611I

open CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

@[expose] noncomputable def invNL (e : SUid frob m) : (Fin m → K) →ₗ[K] (Fin m → K) where
  toFun := invN e
  map_add' := invN_add e
  map_smul' := invN_smul e

theorem exists_herm_eq_dual (ψ : Module.Dual K (Fin m → K)) :
    ∃ c : Fin m → K, ∀ w, ψ w = herm frob c w := by
  refine ⟨fun i => frob (ψ fun j => if i = j then 1 else 0), fun w => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ ψ w, herm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frob_frob, smul_eq_mul, mul_comm]

theorem exists_invN_eq_of_perp {e : SUid frob m} (he : e * e = 1) {z : Fin m → K}
    (hz : ∀ b, invN e b = 0 → herm frob z b = 0) : ∃ c, invN e c = z := by
  have hmem : hermL frob z ∈ (LinearMap.ker (invNL e)).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro b hb
    exact hz b hb
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨ψ, hψ⟩ := hmem
  obtain ⟨c, hc⟩ := exists_herm_eq_dual ψ
  refine ⟨c, ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_herm frob fun b => ?_
  have h1 : herm frob z b = herm frob c (invN e b) := by
    rw [← hermL_apply, ← hψ, LinearMap.dualMap_apply, hc]
    rfl
  rw [sub_eq_add_neg, herm_add_left, herm_neg_left, herm_invN_left he, h1, add_neg_cancel]

end CFSG.LargeExtraspecial.Asc611I
