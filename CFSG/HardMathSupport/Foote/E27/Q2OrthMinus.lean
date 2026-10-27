module

public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Data.CFSGNative.He.Fp
public import Certificates.Data.E27Table

public section

namespace CFSG.HardMathSupport.Foote.E27.Q2

open CFSG.Sporadic.He.Native CFSG.HardMathSupport.Foote.E27 CFSG.Assembly.LowTwoRank Matrix

abbrev IM (n : ℕ) : Type := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2

theorem bc_of_irred {F : Type} [Field F] (σ : F ≃+* ZMod 2) {b c : F}
    (h : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : σ b = 1 ∧ σ c = 1 := by
  have h0 := h 0
  have h1 := h 1
  have hc : σ c = 1 := by
    have : σ c ≠ 0 := by
      intro hc
      apply h0
      have := σ.injective (hc.trans (map_zero σ).symm)
      simpa using this
    revert this
    generalize σ c = x
    decide +revert
  refine ⟨?_, hc⟩
  have : σ b ≠ 0 := by
    intro hb
    apply h1
    apply σ.injective
    simp [hb, hc, map_add, map_mul, map_pow]
    decide
  revert this
  generalize σ b = x
  decide +revert

theorem quadMinus_comp {F : Type} [Field F] (n : ℕ) (σ : F ≃+* ZMod 2) {b c : F}
    (h : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (v : IM n → F) :
    StatedQuadMinus n (ZMod 2) 1 1 (fun i => σ (v i)) = σ (StatedQuadMinus n F b c v) := by
  obtain ⟨hb, hc⟩ := bc_of_irred σ h
  simp [StatedQuadMinus, map_sum, map_mul, map_add, map_pow, hb, hc]

end CFSG.HardMathSupport.Foote.E27.Q2

end
