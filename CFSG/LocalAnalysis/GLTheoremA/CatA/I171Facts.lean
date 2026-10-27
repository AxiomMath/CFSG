module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def I171LieShape (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .A n q => q.p = 2 ∧ p ∣ Nat.gcd (n + 1) (q.card - 1)
  | .twistedA n q => q.p = 2 ∧ p ∣ Nat.gcd (n + 1) (q.card + 1)
  | .E6 q => p = 3 ∧ q.p = 2 ∧ 3 ∣ q.card - 1
  | .twistedE6 q => p = 3 ∧ q.p = 2 ∧ 3 ∣ q.card + 1
  | _ => False

@[expose] def I171LieShapeAt {G : Type} [Group G] [Finite G] (p : ℕ) (K : Subgroup G) : Prop :=
  catalogIs (PSimple p K) (onLie (I171LieShape p))

@[expose] def I171ShapeFact15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J E : Subgroup G) (d : G),
    p.Prime → p ≠ 2 → IsQuasisimple ↥L → IsChevSimple 2 (PSimple p L) →
    CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ 2 →
    E ≤ Subgroup.normalizer (L : Set G) → InnDiagOn p E L →
    E ⊓ Subgroup.centralizer (L : Set G) = ⊥ → d ∈ E → d ≠ 1 →
    GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) J →
    ∀ b ∈ E, (b ∈ Subgroup.normalizer (J : Set G) ∧ InnDiagOn p (Subgroup.zpowers b) J) ∨
      I171LieShapeAt p L

end CFSG.LocalAnalysis.GLTheoremA.I171

end
