module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBIsoAt

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

@[expose] def Sec8Case : Prop :=
  (Nonempty (h.J ⧸ pPrimeCore 2 h.J ≃* alternatingGroup (Fin 6)) ∧
      conjugate h.K h.a = h.K ∧ Nonempty (h.K ⧸ pPrimeCore 2 h.K ≃* alternatingGroup (Fin 8))) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f) ∧
      conjugate h.K h.a = h.K ∧ Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 p f

@[expose] def Sec8CaseZ : Prop :=
  (Nonempty (h.J ⧸ pPrimeCore 2 h.J ≃* alternatingGroup (Fin 6)) ∧
      conjugate h.K h.a = h.K ∧
      Nonempty (h.K ⧸ Open.fusionZStar h.K ≃* alternatingGroup (Fin 8))) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f) ∧
      conjugate h.K h.a = h.K ∧ Blueprint.LieModel (h.K ⧸ Open.fusionZStar h.K) .PSp 2 p f

end Hyp52

@[expose] def Lemma81Statement : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H), h.Sec8CaseZ → 8 ≤ Nat.card h.P →
    Nonempty (generalizedFitting H ≃* alternatingGroup (Fin 10)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        (Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f) ∨
          (p = 3 ∧ f = 1 ∧ Nonempty (h.J ⧸ pPrimeCore 2 h.J ≃* alternatingGroup (Fin 6)))) ∧
        (Blueprint.LieModel (generalizedFitting H) .PSL 4 p f ∨
          Blueprint.LieModel (generalizedFitting H) .PSU 4 p f)

@[expose] def Sec8Setting (X : Type) [Group X] [Finite X] (h : Hyp52 X) : Prop :=
  IsSimpleGroup X ∧ (∃ u v : X, u * v ≠ v * u) ∧ Assembly.KProper Blueprint.Catalog X ∧
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) ∧
    ¬ OutcomeLocal.UOutcome X ∧ GSMaximalUnbalancingTriple h.a h.x h.J ∧ SmallType h.J ∧
    GSIsoAt h.a h.J ∧
    ¬ ConclusionB1 h.J ∧ ¬ ConclusionB2a h.a h.J ∧ h.Sec8Case

@[expose] def Lemma82Statement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (h : Hyp52 X), Sec8Setting X h → Nat.card h.P = 4

@[expose] def Lemma83Statement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (h : Hyp52 X), Sec8Setting X h → Nat.card h.P ≠ 4

theorem sec8_false (h82 : Lemma82Statement) (h83 : Lemma83Statement) {X : Type} [Group X]
    [Finite X] (h : Hyp52 X) (hset : Sec8Setting X h) : False :=
  h83 X h hset (h82 X h hset)

end CFSG.ComponentClassification.GSThmB
