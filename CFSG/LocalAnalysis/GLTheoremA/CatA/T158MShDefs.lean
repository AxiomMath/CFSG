module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def t158Shape (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  t158ShapeA p i ∨ t158ShapeTwA p i ∨ t158ShapeE6 p i ∨ t158ShapeTwE6 p i

@[expose] def T158Norm : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    catalogIs (PSimple p K) (t158Shape p) → T158Hyp p K B x₁ x₂ L₁ L₂ →
      InnDiagOn p (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) K →
        B ≤ Subgroup.normalizer (K : Set X)

structure PreSetup {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) :
    Prop where
  prime : p.Prime
  odd : p ≠ 2
  qs : CFSG.Open.IsQuasisimple ↥L
  core : GLAPPrimeCore p ↥L = ⊥
  chev2 : IsChevSimple 2 (PSimple p L)
  elem : IsElemAbelian p A
  norm : A ≤ Subgroup.normalizer (L : Set G)
  idiag₂ : InnerDiagMarking (Subgroup.zpowers d ⊔ Subgroup.zpowers b) L
  faithful : A ⊓ Subgroup.centralizer (L : Set G) = ⊥
  d_mem : d ∈ A
  d_ne : d ≠ 1
  b_mem : b ∈ A
  pcomp : GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) J
  chevJ : IsChevSimple 2 (PSimple p J)
  b_norm : b ∈ Subgroup.normalizer (J : Set G)
  fg : FGOn p b J

@[expose] def T158SetupLU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (N : ℕ),
    PreSetup p L J A d b →
    catalogIs (PSimple p L) (onLie fun i => ∃ q,
      (i = .A (N - 1) q ∨ i = .twistedA (N - 1) q) ∧ I171.I171LieShape p i) →
    T171Sh.Setup p L J A d b ∧ 2 * p ≤ N

@[expose] def T158SetupE6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G),
    PreSetup 3 L J A d b →
    catalogIs (PSimple 3 L) (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧
      (i = .E6 q ∨ i = .twistedE6 q)) →
    T171Sh.Setup 3 L J A d b

@[expose] def T158IdentU6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G) (n : ℕ),
    PreSetup 3 L J A d b → catalogIs (PSimple 3 L) (S10.isU6n n) → Odd n →
      catalogIs (PSimple 3 J) (S10.isL2n (3 * n))

@[expose] def T158IdentTwE6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G) (n : ℕ),
    PreSetup 3 L J A d b → catalogIs (PSimple 3 L) (S10.isTE6n n) → Odd n →
      catalogIs (PSimple 3 J) (S10.isU3n (3 * n))

@[expose] def T158FixL2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (J : Subgroup X) (x : X) (n : ℕ),
    x ^ 3 = 1 → FGOn 3 x J → catalogIs (PSimple 3 J) (S10.isL2n (3 * n)) →
      ∀ M : Subgroup X, GLAPComponent 3 (J ⊓ Subgroup.centralizer ({x} : Set X)) M →
        catalogIs (PSimple 3 M) (S10.isL2n n)

@[expose] def T158FixU3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y J : Subgroup X) (x : X) (n : ℕ),
    GLAPComponent 3 Y J → x ^ 3 = 1 → FGOn 3 x J → catalogIs (PSimple 3 J) (S10.isU3n (3 * n)) →
      ∀ M : Subgroup X, GLAPComponent 3 (J ⊓ Subgroup.centralizer ({x} : Set X)) M →
        catalogIs (PSimple 3 M) (S10.isU3n n)

@[expose] def LowerTwE6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
    CFSG.Open.IsQuasisimple ↥L →
    catalogIs (PSimple 3 L) (onLie fun i => ∃ q, i = .twistedE6 q ∧
      q.p = 2 ∧ 3 ∣ q.card + 1) →
    ∃ E U : Subgroup G, E ≤ L ∧ U ≤ L ∧ IsElemAbelian 3 E ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (U : Set G) ∧
      3 ^ 4 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card E

end CFSG.LocalAnalysis.GLTheoremA.T158

end
