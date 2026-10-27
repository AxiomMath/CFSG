module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def CatHaradaAS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → Catalog ↥S → centralizer (S : Set G) = ⊥ →
    ∀ t : G, orderOf t = 2 →
    Nonempty (↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) →
    HaradaOneList G

@[expose] def CatHaradaTwoAS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → Catalog ↥S → centralizer (S : Set G) = ⊥ →
    ∀ t v : G, orderOf t = 2 → v * v = 1 → ∀ J : Subgroup G,
      Nonempty (↥J ≃* Equiv.Perm (Fin 5)) →
      (zpowers t ⊔ zpowers v) ⊓ J = ⊥ → (∀ a ∈ zpowers t ⊔ zpowers v, ∀ b ∈ J, a * b = b * a) →
      centralizer ({t} : Set G) = (zpowers t ⊔ zpowers v) ⊔ J →
      centralizer ({v} : Set G) = centralizer ({t} : Set G) →
      centralizer ({t * v} : Set G) = centralizer ({t} : Set G) → False

@[expose] def CatHarrisAS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → Catalog ↥S → centralizer (S : Set G) = ⊥ →
    ∀ t : G, orderOf t = 2 →
    Nonempty (↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) →
    LieModel ↥S .PSU 4 3 1 ∨ IsSporadic ↥S .HS ∨ LieModel ↥S .PSL 3 3 2 ∨ LieModel ↥S .PSL 4 3 1

@[expose] def CatCentFour : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → Catalog S →
    ∀ V : Subgroup S, Nat.card V = 4 → (∀ w ∈ V, w ≠ 1 → centralizer ({w} : Set S) = V) →
    Nonempty (S ≃* alternatingGroup (Fin 5))

@[expose] def NoFifteen : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (LieModel S .PSU 4 3 1 ∨ LieModel S .PSL 3 3 2 ∨ LieModel S .PSL 4 3 1) →
    ∀ x : S, orderOf x ≠ 15

@[expose] def OutNoOdd : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (LieModel S .PSU 4 3 1 ∨ LieModel S .PSL 3 3 2 ∨ LieModel S .PSL 4 3 1) →
    ∀ σ : MulAut S, Odd (orderOf σ) → σ ∈ (MulAut.conj : S →* MulAut S).range

end CFSG.EvenSporadicStandard.HSStd.InvCent
