module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf innerAut)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped MatrixGroups

namespace Prop1310a5

@[expose] def fixedSub {K : Type} [Group K] (σ : MulAut K) : Subgroup K where
  carrier := {k | σ k = k}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv, ha]

@[expose] def Input23_19 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ B : Subgroup X, IsElemAbelian p B → 4 ≤ CFSG.Open.pRank p B →
      CFSG.Open.pRank p B = CFSG.Open.pRank p (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      ((∃ n : ℕ, IsAltType n (K ⧸ Subgroup.center K)) ∨ (∃ q : ℕ, q ≠ p ∧ IsLieChar (· = q) K) ∨
        (∀ A : Subgroup (MulAut K), IsElemAbelian p A → CFSG.Open.pRank p A ≤ 2)) →
      K ≤ GLBCore p 2 B

end Prop1310a5

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
