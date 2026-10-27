module

public import CFSG.GH74.L5U5.ModelsBridge

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.Blueprint Subgroup

section Shapes

variable {G : Type} [Group G]

@[expose] def ShapeS1 (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  IsSL4Model ↥K ∧ xbar x ∈ K

@[expose] def ShapeS2 (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
    Nonempty (↥K ≃* StatedSp 2 F)) ∧ xbar x ∈ K

@[expose] def ShapeS3 (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
    (LieModel ↥K .PSL 3 p f ∨ LieModel ↥K .PSU 3 p f)) ∧ xbar x ∉ K

@[expose] def ShapeS4 (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  (∃ f : ℕ, LieModel ↥K .twistedG2 0 3 f) ∧ xbar x ∉ K

@[expose] def ShapeS5 (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  NativeSporadic.IsSporadic ↥K .J1 ∧ xbar x ∉ K

@[expose] def GenericShape (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  ShapeS1 x K ∨ ShapeS2 x K ∨ ShapeS3 x K ∨ ShapeS4 x K ∨ ShapeS5 x K

end Shapes

@[expose] def NoTwoCover (S : Type) [Group S] : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) →
    Nonempty (K ⧸ center K ≃* S) → center K = ⊥

@[expose] def NoTwoCoverGen4 (S : Type) [Group S] : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) → Gen4 K →
    Nonempty (K ⧸ center K ≃* S) → center K = ⊥

theorem NoTwoCover.gen4 {S : Type} [Group S] (h : NoTwoCover S) : NoTwoCoverGen4 S :=
  fun K _ _ hK h2 _ e => h K hK h2 e

structure GenericKnownFacts : Prop where
  alt_cover : ∀ n : ℕ, 7 ≤ n → n ≤ 11 → ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K →
    IsPGroup 2 ↥(center K) → Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n)) →
      Nat.card (center K) ≤ 2
  psl2_cover : ∀ p f : ℕ, p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K →
    IsPGroup 2 ↥(center K) → LieModel (K ⧸ center K) .PSL 2 p f →
      center K = ⊥ ∨ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (K ≃* StatedSL 2 F)
  psp4_cover : ∀ p f : ℕ, p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K →
    IsPGroup 2 ↥(center K) → LieModel (K ⧸ center K) .PSp 2 p f →
      center K = ⊥ ∨ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (K ≃* StatedSp 2 F)
  psl4_cover : ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) →
    ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
      ∀ e : K ⧸ center K ≃* StatedProj (StatedSL 4 F),
        ∃ π : StatedSL 4 F →* K, Function.Surjective π ∧
          ∀ g, e (QuotientGroup.mk (π g)) = QuotientGroup.mk g
  psu4_cover : ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) →
    ∀ (F : Type) [Field F] [Finite F] (q : ℕ), Nat.card F = q ^ 2 → Odd q →
      ∀ e : K ⧸ center K ≃* StatedProj (StatedSU 4 q F),
        ∃ π : StatedSU 4 q F →* K, Function.Surjective π ∧
          ∀ g, e (QuotientGroup.mk (π g)) = QuotientGroup.mk g
  noTwoCover_psl3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → ∀ (S : Type) [Group S],
    LieModel S .PSL 3 p f → NoTwoCover S
  noTwoCover_psu3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → ∀ (S : Type) [Group S],
    LieModel S .PSU 3 p f → NoTwoCover S
  noTwoCover_g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → ∀ (S : Type) [Group S],
    LieModel S .G2 0 p f → NoTwoCover S
  noTwoCover_3D4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → ∀ (S : Type) [Group S],
    LieModel S .trialityD4 0 p f → NoTwoCover S
  noTwoCover_ree : ∀ f : ℕ, ∀ (S : Type) [Group S], LieModel S .twistedG2 0 3 f → NoTwoCover S
  noTwoCover_J1 : ∀ (S : Type) [Group S], NativeSporadic.IsSporadic S .J1 → NoTwoCover S
  noTwoCover_McL : ∀ (S : Type) [Group S], NativeSporadic.IsSporadic S .McL → NoTwoCoverGen4 S
  noTwoCover_Ly : ∀ (S : Type) [Group S], NativeSporadic.IsSporadic S .Ly → NoTwoCoverGen4 S
  noTwoCover_psl5 : ∀ p f : ℕ, p.Prime → p ^ f % 4 = 3 → ∀ (S : Type) [Group S],
    LieModel S .PSL 5 p f → NoTwoCover S
  noTwoCover_psu5 : ∀ p f : ℕ, p.Prime → p ^ f % 4 = 1 → ∀ (S : Type) [Group S],
    LieModel S .PSU 5 p f → NoTwoCover S
  rank_3D4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S],
    LieModel S .trialityD4 0 p f → ¬ SectionalTwoRankLE S 3

end CFSG.GH74.Generic
