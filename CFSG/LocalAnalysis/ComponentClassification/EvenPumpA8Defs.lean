module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf

@[expose] def A8PumpOutcome (S : Type) [Group S] : Prop :=
  (∃ n : ℕ, Even n ∧ 8 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
    Blueprint.LieModel S .PSL 4 2 2 ∨ Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .HS)

@[expose] def A8PumpLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    Blueprint.Catalog S → ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    Open.fusionZStar ↥P = pPrimeCore 2 ↥P →
    Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 8)) →
      (∃ n : ℕ, Even n ∧ 8 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
      Blueprint.LieModel S .PSL 4 2 2 ∨ Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .HS)

@[expose] def A8PumpSporadicClause : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ x y : S, x * y ≠ y * x) →
    Blueprint.NativeSporadic.SporadicRep S → ∀ (σ : MulAut S) (P : Subgroup S),
    ProperFixedComponent σ P → Open.fusionZStar ↥P = pPrimeCore 2 ↥P →
    Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 8)) → A8PumpOutcome S

@[expose] def A8PumpInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
      (Open.fusionZStar T).map T.subtype ≤
        (pPrimeCore 2 T).map T.subtype ⊔ (Open.fusionZStar M).map M.subtype →
      Nonempty (T ⧸ Open.fusionZStar T ≃* alternatingGroup (Fin 8)) →
      (∃ m' : ℕ, Even m' ∧ 8 ≤ m' ∧
          Nonempty (M ⧸ Open.fusionZStar M ≃* alternatingGroup (Fin m'))) ∨
        Blueprint.LieModel (M ⧸ Open.fusionZStar M) .PSL 4 2 2 ∨
        Nonempty (M ⧸ Open.fusionZStar M ≃* Blueprint.NativeSporadic.Carrier .HS)

end CFSG.ComponentClassification.EvenPump
