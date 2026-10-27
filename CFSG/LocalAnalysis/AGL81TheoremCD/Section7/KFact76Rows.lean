module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open CFSG.RankThree.PartTwo.Sec4
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree (Real3)

@[expose] def RankThreeCover (S : Type) [Group S] : Prop :=
  ∃ (L : Type) (_ : Group L) (_ : Finite L), CFSG.IsQuasisimple L ∧
    IsPGroup 3 (Subgroup.center L) ∧ Nonempty (L ⧸ Subgroup.center L ≃* S) ∧
    CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 3

@[expose] def ListRow76 (S : Type) [Group S] [Finite S] : Prop :=
  ∀ z : S, orderOf z = 3 → RonanK432.WeaklyClosed (Subgroup.zpowers z) →
    CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1 ∨
      (((∃ q : TauCeti.PrimePower, ∃ hv : (TauCeti.LieTypeIndex.G2 q).Valid, q.p ≠ 3 ∧
          Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)) ∨
        (∃ q : TauCeti.PrimePower, ∃ hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid,
          q.card = 3 ∧ Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)) ∨
        Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .J2).Group)) ∧
        Real3 S ∧ RonanK432.NoCover3 S)

@[expose] def OuterRow76RankThree (S : Type) [Group S] [Finite S] : Prop :=
  3 ∣ Nat.card S → ∀ σ : MulAut S, σ ^ 3 = 1 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    (∃ (L : Type) (_ : Group L) (_ : Finite L) (α : MulAut L) (π : L ⧸ Subgroup.center L ≃* S),
      CFSG.IsQuasisimple L ∧ IsPGroup 3 (Subgroup.center L) ∧ α ^ 3 = 1 ∧
      (∀ x : L, π (QuotientGroup.mk (α x)) = σ (π (QuotientGroup.mk x))) ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 3 ∧
      CFSG.Open.pRank 3 (α.toMonoidHom.eqLocus (MonoidHom.id L)) ≤ 2) →
    ¬ RonanK432.AutWeaklyClosed σ

@[expose] def Row76 (S : Type) [Group S] [Finite S] : Prop :=
  ListRow76 S ∧ OuterRow76RankThree S

@[expose] def Rows76RankThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    CFSG.Open.IsCatalogGroup S → 3 ∣ Nat.card S → RankThreeCover S → Row76 S

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
