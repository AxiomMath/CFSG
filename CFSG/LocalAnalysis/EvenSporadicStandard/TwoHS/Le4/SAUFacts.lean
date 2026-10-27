module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Data
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Matrix

structure UFactsQ : Prop where
  fcard : fVecs.length = 8 ∧ fVecs.Nodup
  tnot : tVec ∉ fVecs
  uniq : ∀ v : V4, v + v ∈ fVecs →
    (∀ A ∈ q0List, (A *ᵥ v - v) + (A *ᵥ v - v) = 0) → v + v = 0
  comm : ∃ A ∈ q0List, ∀ v : V4, v + v ∈ fVecs →
    (∃ w : V4, v = w - A *ᵥ w) ∨ (∃ w : V4, v - tVec = w - A *ᵥ w)
  sqprod : ∀ B ∈ q0List, ∃ A₁ ∈ q0List, ∃ A₂ ∈ q0List,
    B = A₁ * A₁ * (A₂ * A₂) ∨ B = -(A₁ * A₁ * (A₂ * A₂))

structure UFactsOf (sl : List M4) : Prop where
  lam_inv : ∀ B ∈ sl, ∀ v : V4, v + v ∈ fVecs → (B *ᵥ v) + (B *ᵥ v) ∈ fVecs
  fx : ∀ B ∈ sl, B * B = 1 → (∃ v ∈ fVecs, B *ᵥ (tVec + v) = tVec + v) ∨
    (∀ w : V4, (w + B *ᵥ w) + (w + B *ᵥ w) = 0 → w + w ∈ fVecs)
  ker : ∀ B ∈ sl, (∀ v : V4, v + v = 0 → B *ᵥ v = v) → B = 1 ∨ B = -1

end CFSG.EvenSporadicStandard.TwoHS
