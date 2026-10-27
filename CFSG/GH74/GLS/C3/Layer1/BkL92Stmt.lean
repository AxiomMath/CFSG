module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

@[expose] def fixSub (K : Type) [Group K] (w : MulAut K) : Subgroup K :=
  MonoidHom.eqLocus (w : K ≃* K).toMonoidHom (MonoidHom.id K)

@[expose] def gammaAut (K : Type) [Group K] (W : Subgroup (MulAut K)) : Subgroup K :=
  ⨆ (w : MulAut K) (_ : w ∈ W) (_ : orderOf w = 2), fixSub K w

@[expose] def B_ivk_6 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W : Subgroup (MulAut K)),
    (HasL2Model K Odd ∨ Nonempty (K ≃* alternatingGroup (Fin 7))) →
    IsPGroup 2 ↥W → 2 ≤ CFSG.pRank 2 ↥W → gammaAut K W ≠ ⊤ →
      (HasL2Model K Odd → ∃ q ∈ ({5, 7, 9} : Finset ℕ), HasL2Model K (fun r => r = q)) ∧
      (CFSG.IsElementaryAbelian 2 ↥W ∧ Nat.card ↥W = 4) ∧
      W ≤ (MulAut.conj : K →* MulAut K).range

end CFSG.GH74.GLS.C3.Layer1.Bk
