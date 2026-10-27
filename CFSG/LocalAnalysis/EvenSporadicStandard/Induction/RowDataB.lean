module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Embed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

@[expose] def OutTwoCovers (S : List TauCeti.SporadicName) : Prop :=
  ∀ s ∈ S, ∀ (H : Type) [Group H] (M : Subgroup H), OddCover s M → OutTwo ↥M

structure Lemma36eDataQ (s : TauCeti.SporadicName) (Q : PairClass) (m e : ℕ) : Prop where
  m_le : m ≤ 2
  data : ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover s L →
    Q H L K u →
      orderOf u = 2 ∧ u ∈ L ∧ K ≤ L ⊓ centralizer ({u} : Set H) ∧
        (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).Characteristic ∧
        CFSG.IsQuasisimple ↥K ∧ Group.IsSolvable ↥(autCentralizer L K) ∧
        twoAdic (autCentralizer L K) ≤ m ∧ ElemBound e (autCentralizer L K) ∧
        (∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g) ∧
        InvolutionFixesNotLam ↥K (2 * e) ∧
        (u ∈ K ∨ u ∈ ⁅L ⊓ centralizer ({u} : Set H), L ⊓ centralizer ({u} : Set H)⁆)

end CFSG.EvenSporadicStandard.Induction
