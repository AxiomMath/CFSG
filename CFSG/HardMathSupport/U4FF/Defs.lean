module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis.RankThreeUC CFSG.QuasithinUnique.Setup.Family

@[expose] def U4RankDichotomy : Prop :=
  ∀ (S : Type) [CommGroup S] [Finite S] [Fact (∀ s : S, s * s = 1)] (n : ℕ)
    (L : Subgroup (MulAut S)), 1 ≤ n → IsU4Group n L → IsIrrOn L →
    NaturalU4Mod n L ∨
      ∀ t ∈ L, t ≠ 1 → t * t = 1 →
        4 * n + 2 ≤ Module.finrank (ZMod 2)
          (LinearMap.range ((binaryLin t : Additive S →ₗ[ZMod 2] Additive S) - 1))

end CFSG.HardMathSupport.U4FF
