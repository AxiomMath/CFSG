module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSpin

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.RootSystem (roots)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)

section Graph

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def sigmaD4Equiv : e6ScLevi K e6D4Nodes ≃* e6ScLevi K e6D4Nodes where
  toFun := sigmaScLevi rhoPerm_mem_e6D4Nodes'
  invFun := sigmaScLevi rhoPerm_mem_e6D4Nodes'
  left_inv x := sigmaScLevi_sigmaScLevi rhoPerm_mem_e6D4Nodes' x
  right_inv x := sigmaScLevi_sigmaScLevi rhoPerm_mem_e6D4Nodes' x
  map_mul' x y := map_mul (sigmaScLevi rhoPerm_mem_e6D4Nodes') x y

@[expose] noncomputable def spinD4Graph : MulAut (spinGroup (quadPlus 4 K)) :=
  ((spinEquivD4 K).trans (sigmaD4Equiv K)).trans (spinEquivD4 K).symm

variable {K}

theorem spinEquivD4_spinD4Graph (g : spinGroup (quadPlus 4 K)) :
    spinEquivD4 K (spinD4Graph K g) = sigmaD4Equiv K (spinEquivD4 K g) := by
  simp only [spinD4Graph, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

theorem spinD4Graph_x {γ : Fin 4 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD 4) ∅) (c : K) :
    spinD4Graph K (SpinPlus.x 4 K three_le_rank_D4 γ c) =
      SpinPlus.x 4 K three_le_rank_D4 (d4Swap γ) c := by
  apply (spinEquivD4 K).injective
  rw [spinEquivD4_spinD4Graph]
  apply Subtype.ext
  change sigma K (RingHom.id K) (spinToE6Sc K (SpinPlus.x 4 K three_le_rank_D4 γ c)) =
    spinToE6Sc K (SpinPlus.x 4 K three_le_rank_D4 (d4Swap γ) c)
  exact sigma_spinToE6Sc_x hγ c

end Graph

end CFSG.SeitzReduction.F4Pilot
