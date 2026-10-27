module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

@[expose] def B_ivk_10_2L : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (q : ℕ), IsFM9 q → HasL2Model K (fun r => r = q) →
    ∀ (y : MulAut K) (H : Subgroup (MulAut K)),
      (MulAut.conj : K →* MulAut K).range ≤ H → y ^ 2 = 1 →
      pPrimeCoreOf 2 (H ⊓ centralizer ({y} : Set (MulAut K))) ≠ ⊥ →
        y ∉ (MulAut.conj : K →* MulAut K).range ∧
        IVK.IsPGL2 ↥((MulAut.conj : K →* MulAut K).range ⊔ zpowers y) (fun r => r = q)

end CFSG.GH74.GLS.C3.Layer1.Bk
