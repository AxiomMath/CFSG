module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209F4
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4InnerCompSU3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

namespace KSF4Out

@[expose] def IsB3EightIndex (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, IsTwoPow q 3 ∧ d = .B 3 q

@[expose] def F4EightCompIndex (d : TauCeti.LieTypeIndex) : Prop :=
  IsB3EightIndex d ∨ KSF4SU3.IsU3EightIndexTwo d

@[expose] def F4EightClass : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (a : X),
    CFSG.Open.IsComponentOf K ⊤ → IsLieQuot ↥K IsF4EightIndex →
      a ∈ Subgroup.normalizer (K : Set X) → a ^ 3 = 1 → a ∉ Subgroup.centralizer (K : Set X) →
        Bal209F4Aux.InnerAt K a →
          (∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
            CFSG.Open.IsQuasisimple ↥J ∧ IsLieQuot ↥J F4EightCompIndex) ∧
          (∀ J₁ J₂ J₃ : Subgroup X,
            GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J₁ →
            GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J₂ →
            GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J₃ →
              J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃)

theorem isB3Eight_bal207 : ∀ d, IsB3EightIndex d →
    Bal207Index 3 d ∧ ¬ CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex d := by
  rintro d ⟨q, hq, rfl⟩
  refine ⟨?_, ?_⟩
  · show 3 = 3 ∧ ((IsTwoPow q 1 ∧ 3 ≤ 3) ∨ (IsTwoPow q 3 ∧ 2 ≤ 3))
    exact ⟨rfl, Or.inr ⟨hq, by norm_num⟩⟩
  · simp [CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex]

end KSF4Out

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
