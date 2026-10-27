module

public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUp

open CFSG CFSG.RankThree.PartOne
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def altStabilizer (m : ℕ) (F : Finset (Fin m)) : Subgroup (alternatingGroup (Fin m)) :=
  ⨅ i ∈ F, MulAction.stabilizer (alternatingGroup (Fin m)) i

@[expose] def Arrow (X Y : Subgroup G) : Prop :=
  X = Y ∨ ∃ n m : ℕ, Nonempty ((↥X ⧸ pCore 2 ↥X) ≃* alternatingGroup (Fin n)) ∧
    ∃ φ : (↥Y ⧸ pCore 2 ↥Y) ≃* alternatingGroup (Fin m), ∃ F : Finset (Fin m),
      F.card = m - n ∧ (shortU ↥X).map X.subtype ≤ (shortU ↥Y).map Y.subtype ∧ X ≤ Y ∧
        ((X.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 ↥Y))).map φ.toMonoidHom =
          altStabilizer m F

@[expose] def InOmega [Finite G] (X : Subgroup G) : Prop :=
  InClassX ↥X ∧ ∃ N : Subgroup G, IsMaximalTwoLocal N ∧ X ≤ N ∧ (X.subgroupOf N).IsSubnormal

@[expose] def IsBlockOfInX [Finite G] (K L : Subgroup G) : Prop :=
  L ≤ K ∧ (L.subgroupOf K).IsSubnormal ∧ InClassX ↥L

@[expose] def blockProduct (M : Subgroup G) {n : ℕ} (L : Fin n → Subgroup G) : Set G :=
  ((M :: List.ofFn L).map fun K : Subgroup G => (K : Set G)).prod

end CFSG.CGT.PushingUp
