module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Concl

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def SL165EngineFamA : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n d p q : ℕ),
    Fintype.card F = 2 ^ n → p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    2 ≤ rk2Ord p n → 3 * rk2Ord p n ≤ d → (2 ≤ n ∨ 3 ≤ rk2Ord p n) →
    (q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3) →
    ∀ Ã : Subgroup ↥(StatedSL d F), IsElemAbelian p Ã →
      CFSG.Open.pRank p (⊤ : Subgroup ↥(StatedSL d F)) ≤ CFSG.Open.pRank p Ã →
      3 ≤ CFSG.Open.pRank p Ã →
      Concl165Avoid ↥(StatedSL d F) p q Ã
        ((StatedScalars (Fin d) F).subgroupOf (StatedSL d F))

end CFSG.LocalAnalysis.GLTheoremA.Y10F
