module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsSU
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndL44Defs

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem revGL_four_eq_antiDiag :
    (revGL 4 F : Matrix (Fin 4) (Fin 4) F) = YamadaEnd.antiDiag F :=
  rfl

theorem sigmaSL_eq_stdSL :
    YamadaEnd.sigmaSL F = stdSL 4 F (revGL 4 F) (frobeniusEquiv F 2) 1 := by
  refine MulEquiv.ext fun x => ?_
  have h : (YamadaEnd.sigmaSL F x : Matrix (Fin 4) (Fin 4) F) =
      (stdSL 4 F (revGL 4 F) (frobeniusEquiv F 2) 1 x : Matrix (Fin 4) (Fin 4) F) := by
    have h1 : (YamadaEnd.sigmaSL F x : Matrix (Fin 4) (Fin 4) F) = YamadaEnd.antiDiag F *
        (((fieldAutSL (frobeniusEquiv F 2) 4 x)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ *
          YamadaEnd.antiDiag F := rfl
    rw [coe_stdSL_graphField, inv_eq_self_of_mul_self revGL_mul_self, h1, ← map_inv]
    rfl
  exact Subtype.ext h

theorem msigma_eq_slUnitary :
    YamadaEnd.msigma F =
      slUnitary (frobeniusEquiv F 2 : F →+* F) (revGL 4 F : Matrix (Fin 4) (Fin 4) F) := by
  rw [← fixSub_stdSL_graphField revGL_mul_self, ← sigmaSL_eq_stdSL]
  rfl

theorem card_msigma (hF : Nat.card F = 4) : Nat.card (YamadaEnd.msigma F) = 25920 := by
  rw [msigma_eq_slUnitary]
  exact card_slUnitary_four hF fun c => by
    rw [RingEquiv.coe_toRingHom, frobeniusEquiv_apply, frobenius_def]

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
