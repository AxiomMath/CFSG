module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly46e

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def IsSLTwoOver (q : ℕ) (Y : Type) [Group Y] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = q ∧
    Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) F)

@[expose] def Harris81Lemma35Step : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ W : Subgroup G, (∀ a ∈ W, a * a = 1) → Nat.card W = 4 →
    ∀ L : Subgroup G, IsTwoComponentIn L (centralizer (W : Set G)) → IsMTypeSchur p ↥L →
      ∀ k : ℕ, 1 ≤ k → 5 ≤ p ^ k → IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L) →
      L ⊓ W ≠ ⊥ → ∀ w ∈ L ⊓ W, w ≠ 1 → ∀ v ∈ W, v ∉ zpowers w →
      ∀ K : Subgroup G, K = GSThmB.conjClosure L (GSThmB.layerIn (centralizer {w})) →
        w ∈ K ∧ K = ⁅L, GSThmB.layerIn (centralizer {w})⁆ ∧
        IsTwoComponentIn K (centralizer {w}) ∧ K.map (MulAut.conj v).toMonoidHom = K ∧
        L = GSThmB.layerIn (K ⊓ centralizer {v}) ∧
        ((p = 7 ∧ IsSLTwoOver 7 (↥L ⧸ pPrimeCore 2 ↥L) ∧
            IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
            Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 16 ∧
            GrSLit.IsL34Type ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))) ∨
          (p = 5 ∧ IsSLTwoOver 5 (↥L ⧸ pPrimeCore 2 ↥L) ∧ ∃ n : ℕ, 4 ≤ n ∧
            IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
            Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 ∧
            Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
              alternatingGroup (Fin (2 * n + 1)))) ∨
          (p = 3 ∧ IsSLTwoOver 9 (↥L ⧸ pPrimeCore 2 ↥L) ∧ ∃ n : ℕ, 4 ≤ n ∧
            IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
            Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 ∧
            Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
              alternatingGroup (Fin (2 * n)))))

@[expose] def Harris47Q81Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Setting46e t L p f S w z V i j → p = 3 → f = 4 → ∀ i' j' : ℕ,
        ∀ J : Subgroup ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i' * z ^ j'} : Set X)),
          IsPComponent 2 J → ¬ IsOfType (fun (Y : Type) [Group Y] =>
            Blueprint.LieModel Y .PSL 4 3 1 ∨ Blueprint.LieModel Y .PSU 4 3 1) ↥J

@[expose] def L4U4InvolutionCentralizerFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Q : Subgroup G) (x : G) (p k m : ℕ), p.Prime → p ≠ 2 →
    1 ≤ k → IsQuasisimple ↥Q →
    ((Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSL 4 p k ∧
        (Nat.card ↥(center ↥Q) = 1 ∨ (Nat.card ↥(center ↥Q) = 2 ∧ 4 ∣ p ^ k - 1))) ∨
      (Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSU 4 p k ∧
        (Nat.card ↥(center ↥Q) = 1 ∨ (Nat.card ↥(center ↥Q) = 2 ∧ 4 ∣ p ^ k + 1)))) →
    x ∈ normalizer (Q : Set G) → x * x = 1 → x ∉ centralizer (Q : Set G) →
    Blueprint.LieModel ↥(GSThmB.layerIn (Q ⊓ centralizer {x})) .PSL 2 p m →
    m = 2 * k ∧
      ((∃ B : Subgroup G, B ≤ Q ⊓ centralizer {x} ∧ center ↥B = ⊥ ∧
          ∃ A : Subgroup G, A ≤ B ∧ GrSLit.IsElemTwo A ∧ Nat.card A = 8) ∨
        ∀ w ∈ GSThmB.layerIn (Q ⊓ centralizer {x}), orderOf w = 2 →
          ∃ X₁ X₂ : Subgroup G, X₁ ≠ X₂ ∧ X₁ ≤ Q ⊓ centralizer {w} ∧
            X₂ ≤ Q ⊓ centralizer {w} ∧ (X₁.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal ∧
            (X₂.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal ∧
            X₁ ≤ centralizer (X₂ : Set G) ∧ X₁ ⊓ X₂ = zpowers w ∧
            IsSLTwoOver (p ^ k) ↥X₁ ∧ IsSLTwoOver (p ^ k) ↥X₂)

@[expose] def L34CoverInvolutionFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J : Subgroup G) (x : G), ⁅J, J⁆ = J →
    GrSLit.IsL34Type (↥J ⧸ Open.fusionZStar ↥J) →
    Nat.card ↥(GrSLit.zStarIn J) = 16 * Nat.card ↥(GrSLit.oddIn J) →
    x ∈ normalizer (J : Set G) → x * x = 1 →
    IsPGroup 2 (↥(J ⊓ centralizer {x}) ⧸ pPrimeCore 2 ↥(J ⊓ centralizer {x})) →
    ∃ E : Subgroup G, E ≤ J ⊓ centralizer {x} ∧ GrSLit.IsElemTwo E ∧
      Nat.card ↥(E ⊓ GrSLit.zStarIn J) = 4 ∧
      (x ∈ GrSLit.withKernel J → Nat.card E = 16) ∧ (x ∉ GrSLit.withKernel J → Nat.card E = 8)

@[expose] def AlternatingCoverInvolutionFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J : Subgroup G) (x : G) (m : ℕ), 8 ≤ m → ⁅J, J⁆ = J →
    Nonempty (↥J ⧸ Open.fusionZStar ↥J ≃* alternatingGroup (Fin m)) →
    x ∈ normalizer (J : Set G) → x * x = 1 →
    ¬ IsPGroup 2 (↥(J ⊓ centralizer {x}) ⧸ pPrimeCore 2 ↥(J ⊓ centralizer {x}))

end CFSG.ComponentClassification.HarrisLit
