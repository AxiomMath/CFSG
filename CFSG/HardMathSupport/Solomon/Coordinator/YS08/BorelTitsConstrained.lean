module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LieType.BorelTits

@[expose] def LieQConstrained (q : ℕ) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → IsChevOfChar q ↥S → Subgroup.centralizer (S : Set H) = ⊥ →
    ∀ Q : Subgroup H, Q ≤ S → Q ≠ ⊥ → IsPGroup q ↥Q →
      ∀ h ∈ Subgroup.normalizer (Q : Set H),
        (∀ r ∈ pCoreOf q (Subgroup.normalizer (Q : Set H)), h * r = r * h) →
        h ∈ pCoreOf q (Subgroup.normalizer (Q : Set H))

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
