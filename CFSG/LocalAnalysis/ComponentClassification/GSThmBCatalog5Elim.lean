module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypes

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def CFProp23IndexElim : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H),
    ((∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧ Nonempty (OddBar h.J ≃* alternatingGroup (Fin n)) ∧
        conjugate h.K h.a = h.K ∧ Nonempty (OddBar h.K ≃* alternatingGroup (Fin (n + 2)))) ∨
      ((Blueprint.LieModel (OddBar h.J) .PSL 2 5 1 ∨ Blueprint.LieModel (OddBar h.J) .PSL 2 7 1) ∧
        conjugate h.K h.a = h.K ∧ center (OddBar h.K) ≠ ⊥ ∧
        Blueprint.LieModel (ZStarBar h.K) .PSL 3 2 2) ∨
      ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) ∧
          conjugate h.K h.a = h.K ∧ (Blueprint.LieModel (ZStarBar h.K) .PSL 4 p f ∨
            Blueprint.LieModel (ZStarBar h.K) .PSU 4 p f ∨
            ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (ZStarBar h.K) .POmegaMinus 4 p e)) ∧
        h.a ∉ h.K ⊔ coreActionKernel h.K)) →
    h.T ≤ zpowers h.a ⊔ h.B

@[expose] def CFHeNoA5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    Nonempty (↥(generalizedFitting Y) ≃* Blueprint.NativeSporadic.He) →
    ∀ t : Y, orderOf t = 2 → ∀ L : Subgroup Y, L ≤ centralizer ({t} : Set Y) →
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set Y))) →
      ¬ Nonempty (OddBar L ≃* alternatingGroup (Fin 5))

end CFSG.ComponentClassification.GSThmB
