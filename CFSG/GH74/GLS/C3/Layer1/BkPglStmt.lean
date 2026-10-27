module

public import CFSG.GH74.GLS.C3.Layer1.BkL92Stmt
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

@[expose] def B_pgl_K : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (q : ℕ), (q = 7 ∨ q = 9) → HasL2Model K (fun r => r = q) →
    ∀ y : MulAut K, y ∉ (MulAut.conj : K →* MulAut K).range → y ^ 2 = 1 →
      IVK.IsPGL2 ↥((MulAut.conj : K →* MulAut K).range ⊔ zpowers y) (fun r => r = q) →
      ∀ V : Subgroup (MulAut K), V ≤ (MulAut.conj : K →* MulAut K).range →
        CFSG.IsElementaryAbelian 2 ↥V → Nat.card ↥V = 4 →
        IsCoatom (gammaAut K V) ∧
        (∀ φ ∈ (MulAut.conj : K →* MulAut K).range ⊔ zpowers y,
          (∀ k ∈ gammaAut K V, φ k ∈ gammaAut K V) →
            φ ∈ (MulAut.conj : K →* MulAut K).range) ∧
        (∀ v ∈ V, v ≠ 1 → ∃ φ ∈ (MulAut.conj : K →* MulAut K).range ⊔ zpowers y,
          φ ∉ (MulAut.conj : K →* MulAut K).range ∧ φ * v = v * φ)

end CFSG.GH74.GLS.C3.Layer1.Bk
