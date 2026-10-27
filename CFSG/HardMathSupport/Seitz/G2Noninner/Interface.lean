module

public import CFSG.RankThree.PartOne.SEITZ2.G2Outer

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ2 CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley

@[expose] def SubfieldPairG2Odd : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 → ∀ (σ : K ≃+* K) (p : ℕ), p.Prime →
    5 ≤ p → orderOf σ = p → ∀ g : adjointGroup .G2 K,
      (g2Fixed σ).map (MulAut.conj g).toMonoidHom ≠ g2Fixed σ →
      Subgroup.closure ((g2Fixed σ : Set (adjointGroup .G2 K)) ∪
        ((g2Fixed σ).map (MulAut.conj g).toMonoidHom : Set (adjointGroup .G2 K))) = ⊤ ∨
        ¬ p ∣ Nat.card (g2Fixed σ)

end CFSG.HardMathSupport.Seitz.G2Noninner
