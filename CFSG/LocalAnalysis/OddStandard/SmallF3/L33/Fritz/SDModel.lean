module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsClassOuter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsClassInner

public section

namespace CFSG.OddStandard.SmallF3.L33.KD

open CFSG.Blueprint

structure SDModel (L : Type) [Group L] where
  F : FritzData L
  conj_injective : Function.Injective (MulAut.conj : L →* MulAut L)
  card_L : Nat.card L = 5616
  card_aut : Nat.card (MulAut L) = 11232
  index_inner : (MulAut.conj : L →* MulAut L).range.index = 2
  involutions_conj : ∀ {u v : L}, u ^ 2 = 1 → u ≠ 1 → v ^ 2 = 1 → v ≠ 1 → IsConj u v
  card_involutions : Nat.card {u : L // u ^ 2 = 1 ∧ u ≠ 1} = 117
  outer_involutions_conj : ∀ {φ ψ : MulAut L}, φ ^ 2 = 1 →
    (¬ ∃ a : L, ∀ u : L, φ u = a * u * a⁻¹) → ψ ^ 2 = 1 →
      (¬ ∃ a : L, ∀ u : L, ψ u = a * u * a⁻¹) → IsConj φ ψ
  card_outer_involutions :
    Nat.card {φ : MulAut L // φ ^ 2 = 1 ∧ ¬ ∃ a : L, ∀ u : L, φ u = a * u * a⁻¹} = 234

namespace SDModel

theorem exists_sdModel
    {L : Type} [Group L] (hL : LieModel L .PSL 3 3 1) : Nonempty (SDModel L) := by
  obtain ⟨F⟩ := l33_nonempty_fritzData hL
  exact ⟨{
    F := F
    conj_injective := l33_conj_injective hL
    card_L := l33_card_L hL
    card_aut := l33_card_mulAut hL
    index_inner := l33_index_inner hL
    involutions_conj := fun hu hu1 hv hv1 => l33_involutions_conj hL hu hu1 hv hv1
    card_involutions := l33_card_involutions hL
    outer_involutions_conj := fun hφ hφo hψ hψo => l33_outer_involutions_conj hL hφ hφo hψ hψo
    card_outer_involutions := l33_card_outer_involutions hL }⟩

end SDModel

end CFSG.OddStandard.SmallF3.L33.KD
