module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

structure ModuleFacts {A : Type*} [Group A] (Q : Subgroup (MulAut A)) (t : A) : Prop where
  card : Nat.card A = 2 ^ 10
  elemAb : IsElementaryAbelian 2 A
  card_Q : Nat.card Q = 887040
  invariant_ncard : ∀ S : Set A, 1 ∉ S → (∀ g ∈ Q, ∀ s ∈ S, g s ∈ S) →
    S.ncard ∈ ({0, 77, 330, 616, 407, 693, 946, 1023} : Finset ℕ)
  overgroup : ∀ X : Subgroup (MulAut A), Q ≤ X → ¬ 31 ∣ Nat.card X → ¬ 37 ∣ Nat.card X →
    ¬ 43 ∣ Nat.card X → X = Q
  normalizer_derived : ∀ g : MulAut A, (∀ h ∈ ⁅Q, Q⁆, g * h * g⁻¹ ∈ ⁅Q, Q⁆) → g ∈ Q
  derived_simple : IsSimpleGroup ↥⁅Q, Q⁆
  card_derived : Nat.card ↥⁅Q, Q⁆ = 443520
  centralizer_derived : Q ⊓ centralizer ((⁅Q, Q⁆ : Subgroup (MulAut A)) : Set (MulAut A)) = ⊥
  irreducible_derived : ∀ U : Subgroup A, (∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤
  endo_derived : ∀ f : A →* A, (∀ g ∈ ⁅Q, Q⁆, ∀ a, f (g a) = g (f a)) →
    f = 1 ∨ f = MonoidHom.id A
  noOffenders : ∀ Y : Subgroup (MulAut A), Y ≤ Q → IsElementaryAbelian 2 Y → Y ≠ ⊥ →
    Nat.card Y * Nat.card {a : A // ∀ y ∈ Y, y a = a} < 2 ^ 10
  noBilin : ∀ β : A → A → ZMod 2, (∀ a b c, β (a * b) c = β a c + β b c) →
    (∀ a b c, β a (b * c) = β a b + β a c) → (∀ g ∈ Q, ∀ a b, β (g a) (g b) = β a b) → β = 0
  dual_cocycle : ∀ γ : Q → A → ZMod 2, (∀ g a b, γ g (a * b) = γ g a + γ g b) →
    (∀ g h a, γ (g * h) a = γ g a + γ h ((g : MulAut A)⁻¹ a)) →
    ∃ f : A → ZMod 2, (∀ a b, f (a * b) = f a + f b) ∧
      ∀ g a, γ g a = f ((g : MulAut A)⁻¹ a) + f a
  noWedge : ∀ β : A → A → A, (∀ a b c, β (a * b) c = β a c * β b c) →
    (∀ a b c, β a (b * c) = β a b * β a c) → (∀ a, β a a = 1) →
    (∀ g ∈ Q, ∀ a b, β (g a) (g b) = g (β a b)) → ∀ a b, β a b = 1
  noZ4 : ∀ (V : Type) [CommGroup V] (ρ : Q →* MulAut V) (ι : A →* V), Function.Injective ι →
    (∀ g a, ρ g (ι a) = ι ((g : MulAut A) a)) → (∀ v : V, ∃ a, v ^ 2 = ι a) →
    (∀ v : V, v ^ 2 = 1 → ∃ a, v = ι a) → (∀ a, ∃ v : V, v ^ 2 = ι a) → False
  split_of_fixed : ∀ Γ : Q → A → A, (∀ g a b, Γ g (a * b) = Γ g a * Γ g b) →
    (∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut A) (Γ h ((g : MulAut A)⁻¹ a))) →
    (∃ u : A, ∀ g : Q, (g : MulAut A) t = t → Γ g t = u * (g : MulAut A) u) →
    ∃ X : A →* A, ∀ g a, Γ g a = X a * (g : MulAut A) (X ((g : MulAut A)⁻¹ a))

variable {G : Type*} [Group G]

@[expose] def conjN (L A : Subgroup G) : ↥(L ⊓ normalizer (A : Set G)) →* MulAut A :=
  A.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)

@[expose] def autImage (L A : Subgroup G) : Subgroup (MulAut A) := (conjN L A).range

structure JcFacts (L A T : Subgroup G) (t : G) : Prop where
  le : A ≤ L
  t_mem : t ∈ A
  T_le : T ≤ normalizer (A : Set G)
  centralizer_eq : L ⊓ centralizer (A : Set G) = A
  module : ModuleFacts (autImage L A) ⟨t, t_mem⟩
  perfectE : commutator ↥(L ⊓ centralizer ({t} : Set G)) = ⊤
  outE : ∀ α : MulAut ↥(L ⊓ centralizer ({t} : Set G)), ∃ e, α = MulAut.conj e

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
