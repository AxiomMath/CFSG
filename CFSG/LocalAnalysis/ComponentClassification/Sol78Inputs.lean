module

public import CFSG.Open.FusionDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup

@[expose] def AlternatingPumpUpInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
      (Open.fusionZStar T).map T.subtype ≤
        (pPrimeCore 2 T).map T.subtype ⊔ (Open.fusionZStar M).map M.subtype →
    ∀ m : ℕ, Odd m → 7 ≤ m → Nonempty (T ⧸ Open.fusionZStar T ≃* alternatingGroup (Fin m)) →
      (∃ m' : ℕ, Odd m' ∧ m ≤ m' ∧
          Nonempty (M ⧸ Open.fusionZStar M ≃* alternatingGroup (Fin m'))) ∨
        (m = 7 ∧ Nonempty (M ⧸ Open.fusionZStar M ≃* Blueprint.NativeSporadic.He))

end CFSG.ComponentClassification.Sol78
