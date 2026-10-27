module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Defs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def UpD42ExclInnAt (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsCatalogLieIso S P →
    ∀ (b : S) (J A : Subgroup S), b ≠ 1 → b ^ 3 = 1 →
    GLAPComponent 3 (Subgroup.centralizer ({b} : Set S)) J → IsCatalogLieIso ↥J IsD42Index →
    A ≤ J → IsElemAbelian 3 A → Nat.card A = 3 ^ 4 →
    (∀ y ∈ Subgroup.centralizer ({b} : Set S), y ∈ Subgroup.centralizer (J : Set S) →
      y ^ 3 = 1 → y ∈ Subgroup.zpowers b) →
    (∀ y : S, y * b * y⁻¹ ∈ Subgroup.zpowers b ⊔ A → y * b * y⁻¹ ∈ Subgroup.zpowers b) →
    False

end CFSG.HardMathSupport.Dickson.Sec6

end
