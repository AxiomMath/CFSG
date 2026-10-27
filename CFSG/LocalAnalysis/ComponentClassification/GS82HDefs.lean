module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA7
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def GS82HConfig {X : Type} [Group X] (q₀ : ℕ) (t : X) (K R T : Subgroup X) (w : X) :
    Prop :=
  orderOf t = 2 ∧ K ≤ centralizer ({t} : Set X) ∧
    IsPComponent 2 (K.subgroupOf (centralizer ({t} : Set X))) ∧
    IsPGroup 2 R ∧ R ≤ centralizer ({t} : Set X) ∧ R ≤ normalizer (K : Set X) ∧
    T ≤ K ⊓ centralizer (R : Set X) ∧ IsPComponent 2 (T.subgroupOf (K ⊓ centralizer (R : Set X))) ∧
    HarrisLit.IsSLTwoOver q₀ (↥T ⧸ pPrimeCore 2 ↥T) ∧
    orderOf w = 2 ∧ w ∈ T ∧ w ∈ (Open.fusionZStar ↥K).map K.subtype

@[expose] def GS82HAmbient (X : Type) [Group X] [Finite X] : Prop :=
  IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ Assembly.KProper Blueprint.Catalog X ∧
    ¬ Blueprint.Catalog X ∧ (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) ∧
    ¬ OutcomeLocal.UOutcome X

@[expose] def GS82LargeStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X], GS82HAmbient X →
    ∀ (r e : ℕ), r.Prime → r ≠ 2 → 1 ≤ e → r ^ e ∉ ({3, 5, 7, 9} : Finset ℕ) →
    ∀ (t : X) (K R T : Subgroup X) (w : X), ¬ GS82HConfig (r ^ e) t K R T w

@[expose] def GS82LemmaPsi : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (c : Eight2.CtxA0 X),
    ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)) →
    c.s.p = 3 → c.s.f = 1 →
    ∀ d : X, d ∈ c.s.h.P → orderOf d = 2 → d * c.b = c.b * d →
      d ∉ zpowers c.s.h.a ⊔ c.s.h.secB0 c.s.y →
      ¬ ∃ M : Subgroup X, UnbalancedGS.GSIsoCorr c.s.h.a c.s.h.J d M

end CFSG.ComponentClassification.GSThmB
