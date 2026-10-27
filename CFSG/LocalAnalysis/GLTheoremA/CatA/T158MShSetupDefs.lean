module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def T158CompLU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (N : ℕ),
    PreSetup p L J A d b →
    catalogIs (PSimple p L) (onLie fun i => ∃ q,
      (i = .A (N - 1) q ∨ i = .twistedA (N - 1) q) ∧ I171.I171LieShape p i) →
    (CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      GLALayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J) ∧ 2 * p ≤ N ∧
    catalogIs (PSimple p J) (onLie fun i => ∃ q, q.p = 2 ∧
      (i = .A (N / p - 1) q ∨ i = .twistedA (N / p - 1) q))

@[expose] def T158ClaimLU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (N : ℕ),
    PreSetup p L J A d b →
    catalogIs (PSimple p L) (onLie fun i => ∃ q,
      (i = .A (N - 1) q ∨ i = .twistedA (N - 1) q) ∧ I171.I171LieShape p i) →
    GLALayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J →
    catalogIs (PSimple p J) (onLie fun i => ∃ q, q.p = 2 ∧
      (i = .A (N / p - 1) q ∨ i = .twistedA (N / p - 1) q)) →
    ∀ a ∈ A, InnDiagOn p (Subgroup.zpowers a) L

end CFSG.LocalAnalysis.GLTheoremA.T158

end
