module

public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Data.CFSGNative.He.Fp
public import Certificates.Data.E27Table

public section

namespace CFSG.HardMathSupport.Foote.E27.Q2

open CFSG.Sporadic.He.Native CFSG.HardMathSupport.Foote.E27 CFSG.Assembly.LowTwoRank Matrix

theorem quadPlus_comp {F : Type} [Field F] (n : ℕ) (σ : F ≃+* ZMod 2) (v : Fin n ⊕ Fin n → F) :
    StatedQuadPlus n (ZMod 2) (fun i => σ (v i)) = σ (StatedQuadPlus n F v) := by
  simp [StatedQuadPlus, map_sum, map_mul]

end CFSG.HardMathSupport.Foote.E27.Q2

end
