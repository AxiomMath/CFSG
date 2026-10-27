module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def Harris82Theorem1KProper : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ z : G, orderOf z = 2 → ∀ L : Subgroup G, IsTwoComponentIn L (centralizer {z}) → z ∈ L →
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ IsMTypeSchur p ↥L

theorem harris82Theorem1KProper_of_input (hT1 : Harris82Theorem1Input) :
    Harris82Theorem1KProper :=
  fun _ _ _ _ hnonab _ hcat _ hz _ hL hzL _ hp hp2 =>
    not_isMTypeSchur_of_theorem1 hT1 hnonab hcat hz hL hzL hp hp2

theorem not_isMTypeSchur_of_kProper (h : Harris82Theorem1KProper) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog G) (hcat : ¬ Blueprint.Catalog G) {z : G}
    (hz : orderOf z = 2) {L : Subgroup G} (hL : IsTwoComponentIn L (centralizer {z}))
    (hzL : z ∈ L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ IsMTypeSchur p ↥L :=
  h G hnonab hK hcat z hz L hL hzL p hp hp2

namespace T1

@[expose] def IsCoverOf (τ : StatedLieTag) (n p f c : ℕ) (Y : Type) [Group Y] : Prop :=
  IsQuasisimple Y ∧ Nat.card ↥(center Y) = c ∧ Blueprint.LieModel (Y ⧸ center Y) τ n p f

@[expose] def InductionTypeField (p : ℕ) (J : Type) [Group J] : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧
    (IsCoverOf .POmegaOdd 3 p f 2 (J ⧸ pPrimeCore 2 J) ∨
      IsCoverOf .PSL 4 p f (Nat.gcd 4 (p ^ f - 1)) (J ⧸ pPrimeCore 2 J) ∨
      IsCoverOf .PSU 4 p f (Nat.gcd 4 (p ^ f + 1)) (J ⧸ pPrimeCore 2 J) ∨
      IsCoverOf .PSp 2 p f 2 (J ⧸ pPrimeCore 2 J) ∨
      (Even f ∧ IsSLTwoOver (p ^ f) (J ⧸ pPrimeCore 2 J)))

@[expose] def InductionType (p : ℕ) (J : Type) [Group J] : Prop :=
  InductionTypeField p J ∨
  (p = 3 ∧ ((∃ (τ : StatedLieTag) (n : ℕ),
      Blueprint.LieModel (J ⧸ Open.fusionZStar J) τ n 3 1) ∨
    Nonempty (J ⧸ pPrimeCore 2 J ≃* SL(2, ZMod 3))))

@[expose] def KnownRow : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G) →
    Blueprint.Catalog (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
      Open.fusionZStar ↥(GH74.GLS.oPrimeResidual 2 G)) →
    ∀ z : G, orderOf z = 2 → ∀ L : Subgroup G, IsTwoComponentIn L (centralizer {z}) →
      z ∈ L → ∀ p : ℕ, p.Prime → p ≠ 2 → IsMTypeSchur p ↥L → InductionTypeField p ↥L →
        IsChevalleyOver p (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
            pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) ∨
          Nonempty (G ⧸ pPrimeCore 2 G ≃* ↥Blueprint.NativeSporadic.M11)

theorem knownRow_of_input (hT1 : Harris82Theorem1Input) : KnownRow :=
  fun G _ _ hG _ z hz L hL hzL p hp hp2 hM _ => hT1 G hG z hz L (.inl hL) hzL p hp hp2 hM

end T1

end CFSG.ComponentClassification.HarrisLit
