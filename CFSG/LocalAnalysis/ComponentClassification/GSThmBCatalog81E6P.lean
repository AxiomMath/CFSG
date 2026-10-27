module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def GH74List (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (Blueprint.LieModel G .G2 0 p f ∨ Blueprint.LieModel G .trialityD4 0 p f)) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel G .PSp 2 p f) ∨
    (∃ f : ℕ, Blueprint.LieModel G .twistedG2 0 3 f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧
      Blueprint.LieModel G .PSL 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧
      Blueprint.LieModel G .PSU 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ Blueprint.LieModel G .PSL 5 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧ Blueprint.LieModel G .PSU 5 p f) ∨
    (Blueprint.LieModel G .PSL 2 2 3 ∨ Blueprint.LieModel G .PSL 2 2 4 ∨
      Blueprint.LieModel G .PSL 3 2 2 ∨ Blueprint.LieModel G .twistedB2 0 2 3) ∨
    (∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
    (Blueprint.NativeSporadic.IsSporadic G .M12 ∨ Blueprint.NativeSporadic.IsSporadic G .M22 ∨
      Blueprint.NativeSporadic.IsSporadic G .M23 ∨ Blueprint.NativeSporadic.IsSporadic G .J1 ∨
      Blueprint.NativeSporadic.IsSporadic G .J2 ∨ Blueprint.NativeSporadic.IsSporadic G .J3 ∨
      Blueprint.NativeSporadic.IsSporadic G .McL ∨ Blueprint.NativeSporadic.IsSporadic G .Ly)

@[expose] def P211For (C : ∀ (G : Type) [Group G], Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup ↥(generalizedFitting X) →
    centralizer (generalizedFitting X : Set X) = ⊥ → C ↥(generalizedFitting X) →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    ∀ (a : X) (J D : Subgroup X), a * a = 1 → a ≠ 1 → J ≤ centralizer ({a} : Set X) →
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))) →
      IsSec8JType (J ⧸ pPrimeCore 2 J) p f → J ≤ generalizedFitting X → D ≤ J →
      (∃ R : Sylow 2 ↥J, (R : Subgroup ↥J) = D.subgroupOf J) →
      (∀ R : Subgroup X, R ≤ generalizedFitting X → IsPGroup 2 R →
        Nat.card R ≤ 2 * Nat.card D ^ 2) →
    ∀ (b : X) (K : Subgroup X), b * b = 1 → b ≠ 1 → K ≤ centralizer ({b} : Set X) →
      IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set X))) →
      IsSec8Socle (K ⧸ pPrimeCore 2 K) p f →
      Nonempty (↥(generalizedFitting X) ≃* alternatingGroup (Fin 10)) ∨
        Blueprint.LieModel ↥(generalizedFitting X) .PSL 4 p f ∨
        Blueprint.LieModel ↥(generalizedFitting X) .PSU 4 p f

@[expose] def CF81E6P211 : Prop := P211For GH74List

end CFSG.ComponentClassification.GSThmB
