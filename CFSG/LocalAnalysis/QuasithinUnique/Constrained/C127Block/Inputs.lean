module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Inputs
public import CFSG.Quasithin.Background.B69Asm

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace B69

@[expose] def AltShapeK {V : Type} [CommGroup V] (k : ℕ) (M A L : Subgroup (MulAut V))
    (W : Subgroup V) : Prop :=
  ∃ π : Equiv.Perm (Fin (2 * k + 1)) →* ↥(L ⊔ A),
    Function.Surjective π ∧
    (FFModel.symDn (2 * k + 1)).RealizesVia (L ⊔ A) W ⊥ π ∧
    L = (alternatingGroup (Fin (2 * k + 1))).map ((L ⊔ A).subtype.comp π) ∧
    (∃ i j : Fin (2 * k + 1), i ≠ j ∧
      A = (Subgroup.zpowers (Equiv.swap i j)).map ((L ⊔ A).subtype.comp π)) ∧
    ((M ⊓ (L ⊔ A)).subgroupOf (L ⊔ A) =
      (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1)))
        (⟨0, by omega⟩ : Fin (2 * k + 1))).map π)

theorem altShape_iff {V : Type} [CommGroup V] {M A L : Subgroup (MulAut V)} {W : Subgroup V} :
    AltShape M A L W ↔ ∃ k : ℕ, 1 ≤ k ∧ AltShapeK k M A L W :=
  ⟨fun ⟨k, hk, π, h⟩ => ⟨k, hk, π, h⟩, fun ⟨k, hk, π, h⟩ => ⟨k, hk, π, h⟩⟩

@[expose] def AsB69AltDegree : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHypK X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        ∀ k : ℕ, 1 ≤ k → AltShapeK k M A L W → ∃ j : ℕ, 2 * k = 2 ^ j

end B69

end CFSG.Quasithin
