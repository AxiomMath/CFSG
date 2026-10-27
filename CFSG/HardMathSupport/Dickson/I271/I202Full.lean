module

public import CFSG.HardMathSupport.Dickson.I271.Support.EngineGen

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

theorem i202Full_holds :
    ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
      ∀ K B A : Subgroup X, CFSG.Open.IsQuasisimple ↥K → p ∣ Nat.card K →
        B ≤ Subgroup.normalizer (K : Set X) → IsElemAbelian p B → IsSCp p (K ⊔ B) B →
        A ≤ B → ¬ IsCyclic ↥A → IsCompLocallyBalanced p 1 A K →
        (∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
          GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
            B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced p B a J) →
        (∃ a ∈ A, a ≠ 1 ∧ ∀ w ∈ Subgroup.normalizer (K : Set X), Nat.Coprime p (orderOf w) →
          (∀ b ∈ B, ⁅w, b⁆ ∈ Subgroup.centralizer (K : Set X)) →
            ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
              w ∈ Subgroup.normalizer (J : Set X)) →
        IsStronglyBalancedIn p B K := by
  intro X _ _ p hp hp2 K B A hq hpK hBK hBel hSC hAB hAnc hloc hcomp hc
  exact engine_full ⟨hp, hp2, hq, hpK, hBK, hBel, hSC, hAB, hAnc, hloc, hcomp⟩ hc

end CFSG.HardMathSupport.Dickson.I271
