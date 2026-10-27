module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsHarrisIdxTools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts CFSG.Assembly.LowTwoRank

theorem admissible_of_lieModel' {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : Blueprint.LieModel X t n p f) : StatedLieAdmissible t n p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem statedClassicalModel_of_lieModel' {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (h : Blueprint.LieModel X t n p f) :
    StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by rcases ht with rfl | rfl <;> decide)

@[expose] def EvenLieInvolutionOddCoreFact : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (t : StatedLieTag) (n f : ℕ), Blueprint.LieModel J t n 2 f →
    ∀ x : J, orderOf x = 2 → pPrimeCore 2 ↥(centralizer ({x} : Set J)) = ⊥

@[expose] def EvenLieOuterCoverFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsQuasisimple G → pPrimeCore 2 G = ⊥ → center G ≠ ⊥ →
    ∀ (t : StatedLieTag) (n f : ℕ), Blueprint.LieModel (G ⧸ center G) t n 2 f →
    ∀ τ : MulAut G, orderOf τ = 2 → τ ∉ innAut G →
    ∀ p m : ℕ, p.Prime → p ≠ 2 → 1 ≤ m → 16 ∣ p ^ (2 * m) - 1 →
    ∀ K : Subgroup G, IsTwoComponentIn K (fixedPoints τ) →
      (∀ K' : Subgroup G, IsTwoComponentIn K' (fixedPoints τ) → K' = K) →
      Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSL 2 p m →
      (Blueprint.LieModel (G ⧸ center G) .PSL 3 2 2 ∧ Nat.card ↥(center G) < 16) ∨
        Nonempty (G ⧸ center G ≃* alternatingGroup (Fin 8))

@[expose] def PSLTwoOddCharacteristicFact : Prop :=
  ∀ (X : Type) [Group X] (p m : ℕ) (t : StatedLieTag) (n r f : ℕ), p.Prime → p ≠ 2 →
    7 ≤ p ^ m → r ≠ 2 → Blueprint.LieModel X .PSL 2 p m → Blueprint.LieModel X t n r f → r = p

@[expose] def L4U4PartialCoverFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsQuasisimple G → pPrimeCore 2 G = ⊥ → ¬ IsSimpleGroup G →
    ∀ p k : ℕ, p.Prime → p ≠ 2 →
    (Blueprint.LieModel (G ⧸ center G) .PSL 4 p k ∨
      Blueprint.LieModel (G ⧸ center G) .PSU 4 p k) → ¬ IsMType p G →
    ∀ τ : MulAut G, orderOf τ = 2 → ∀ m : ℕ, 1 ≤ m → 16 ∣ p ^ (2 * m) - 1 →
    ∀ K : Subgroup G, IsTwoComponentIn K (fixedPoints τ) →
      (∀ K' : Subgroup G, IsTwoComponentIn K' (fixedPoints τ) → K' = K) →
      Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSL 2 p m → m = 2 * k

end CFSG.ComponentClassification.HarrisLit.N36
