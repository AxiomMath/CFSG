module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.Defs
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def I1416At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (q : ℕ), q.Prime → q ≠ 2 → q ≠ p →
    ∀ (X K J : Subgroup G) (y : G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X K →
      y ∈ Subgroup.normalizer (K : Set G) → y ^ p = 1 → ¬ CentMod p K y →
      GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J →
      IsChevSimple q (PSimple p J) →
      (∃ A : Subgroup (MulAut (PSimple p J)), IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A) →
      IsChevSimple q (PSimple p K)

end CFSG.LocalAnalysis.GLTheoremA
