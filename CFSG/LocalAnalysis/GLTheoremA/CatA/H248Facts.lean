module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.Coordinator.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def CatRankOne (q : ℕ) : TauCeti.CFSGIndex → Prop
  | .lie i =>
    match i.1 with
    | .A 1 Q => Q.p = q
    | .twistedA 2 Q => Q.p = q
    | .reeG2 _ => q = 3
    | _ => False
  | .alternating n _ => (n = 5 ∧ q = 5) ∨ (n = 6 ∧ q = 3)
  | _ => False

@[expose] def CatRankOneGroup (q : ℕ) (S : Type) [Group S] : Prop :=
  catalogIs S (CatRankOne q)

@[expose] def IsU3Shape (p q : ℕ) (S : Type) [Group S] : Prop :=
  ∃ Q : TauCeti.PrimePower, Q.p = q ∧ p ∣ Q.card + 1 ∧
    catalogIs S (onLie fun d => d = .twistedA 2 Q)

@[expose] def RankOneFact : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (S : Type) [Group S] [Finite S], IsChevSimple q S → CatRankOneGroup q S →
      (∃ A : Subgroup (MulAut S), IsElemAbelian p A ∧ p ^ 3 ≤ Nat.card A) → IsU3Shape p q S

@[expose] def CoreFact : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (H : Type) [Group H] [Finite H], CFSG.Open.IsQuasisimple H →
      IsChevSimple q (H ⧸ Subgroup.center H) → ¬ CatRankOneGroup q (H ⧸ Subgroup.center H) →
      (∃ A : Subgroup (MulAut (H ⧸ Subgroup.center H)), IsElemAbelian p A ∧ p ^ 3 ≤ Nat.card A) →
      ¬ IsU3Shape p q (H ⧸ Subgroup.center H) →
      ∀ Q : Subgroup H, IsPGroup q Q → Nat.card Q = q ^ (Nat.card H).factorization q →
        4 ≤ CFSG.Open.pRank q Q ∧ CFSG.HardMathSupport.Solomon.Coordinator.coreIn q 3 Q ⊤ = ⊤

@[expose] def W227 {G : Type} [Group G] (p : ℕ) (K : Subgroup G) : Subgroup ↥K :=
  ⁅CFSG.Open.GLAPPrimeCore p ↥K, ⊤⁆

instance W227.normal {G : Type} [Group G] (p : ℕ) (K : Subgroup G) : (W227 p K).Normal := by
  unfold W227
  infer_instance

@[expose] def M227 {G : Type} [Group G] (p : ℕ) (K : Subgroup G) : Subgroup ↥K :=
  (Subgroup.center (↥K ⧸ CFSG.Open.GLAPPrimeCore p ↥K)).comap
    (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore p ↥K))

instance M227.normal {G : Type} [Group G] (p : ℕ) (K : Subgroup G) : (M227 p K).Normal := by
  unfold M227
  infer_instance

end CFSG.LocalAnalysis.GLTheoremA.H248
