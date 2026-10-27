module

public import CFSG.LargeExtraspecial.S14W4SetDictB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Dict

open Subgroup

variable {X Y : Type*} [Group X] [Finite X] [Group Y] {T : Setting X} {ι : X →* Y}
  {N R : Subgroup Y} {t : Y} (H : Hyp T ι N R t)
include H

theorem irr_of (hirr : ∀ D : Subgroup Y, zpowers t ≤ D → D ≤ N →
      (∀ r ∈ R, ∀ d ∈ D, r * d * r⁻¹ ∈ D) → D = zpowers t ∨ D = N)
    (W : Submodule (ZMod 2) T.Qt) (hW : IsInv T (R.comap ι) W) : W = ⊥ ∨ W = ⊤ :=
  (hirr (DW T ι W) (zpowers_le_DW H W) (DW_le H W) fun _ hr _ hd => DW_conj H W hW hr hd).imp
    (eq_bot_of_DW_eq H) (eq_top_of_DW_eq H)

theorem lattice_of {U₁ U₂ : Subgroup Y} (ht1 : zpowers t ≤ U₁) (h1N : U₁ ≤ N)
    (ht2 : zpowers t ≤ U₂) (h2N : U₂ ≤ N) (hR1 : ∀ r ∈ R, ∀ u ∈ U₁, r * u * r⁻¹ ∈ U₁)
    (hR2 : ∀ r ∈ R, ∀ u ∈ U₂, r * u * r⁻¹ ∈ U₂) (hint : U₁ ⊓ U₂ = zpowers t)
    (hc1 : Nat.card U₁ = 2 ^ 5) (hc2 : Nat.card U₂ = 2 ^ 5)
    (hall : ∀ D : Subgroup Y, zpowers t ≤ D → D ≤ N → (∀ r ∈ R, ∀ d ∈ D, r * d * r⁻¹ ∈ D) →
      D = zpowers t ∨ D = U₁ ∨ D = U₂ ∨ D = N) :
    ∃ W₁ W₂ : Submodule (ZMod 2) T.Qt, IsInv T (R.comap ι) W₁ ∧ IsInv T (R.comap ι) W₂ ∧
      W₁ ⊓ W₂ = ⊥ ∧ Nat.card W₁ = 2 ^ 4 ∧ Nat.card W₂ = 2 ^ 4 ∧
      ∀ W : Submodule (ZMod 2) T.Qt, IsInv T (R.comap ι) W →
        W = ⊥ ∨ W = W₁ ∨ W = W₂ ∨ W = ⊤ := by
  have hinv : ∀ U : Subgroup Y, (∀ r ∈ R, ∀ u ∈ U, r * u * r⁻¹ ∈ U) →
      IsInv T (R.comap ι) (WU T ι U) := fun U hU =>
    WU_isInv (R.comap ι) U fun x hx _ u hu => hU (ι x) hx u hu
  refine ⟨WU T ι U₁, WU T ι U₂, hinv U₁ hR1, hinv U₂ hR2,
    WU_inf_eq_bot H ht1 h1N ht2 h2N hint, ?_, ?_, ?_⟩
  · have := card_WU H ht1 h1N
    omega
  · have := card_WU H ht2 h2N
    omega
  · intro W hW
    rcases hall (DW T ι W) (zpowers_le_DW H W) (DW_le H W)
        (fun _ hr _ hd => DW_conj H W hW hr hd) with hD | hD | hD | hD
    · exact Or.inl (eq_bot_of_DW_eq H hD)
    · exact Or.inr (Or.inl (eq_WU_of_DW_eq H hD))
    · exact Or.inr (Or.inr (Or.inl (eq_WU_of_DW_eq H hD)))
    · exact Or.inr (Or.inr (Or.inr (eq_top_of_DW_eq H hD)))

end CFSG.LargeExtraspecial.S14.W4Dict
