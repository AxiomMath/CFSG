module

public import CFSG.GH74.Uniqueness.SU.SU2Step3c

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

namespace GOPair

variable {X : Type} [Group X] {V : Type} [Group V] [MulDistribMulAction X V] {Y : Subgroup X}

theorem onan_irreducible [Finite X] [Finite V] (hGO : GOPair V Y)
    (hirr : ∀ W : Subgroup V, (∀ x : X, x • W = W) → W = ⊥ ∨ W = ⊤)
    (hno : ∀ N : Subgroup X, N.Normal → N.index ≠ 2) :
    Nat.card V = 8 ∧ Nat.card (fixSub V Y) = 2 ∧ Nat.card X = 21 ∧
      ∃ a b : X, a * b ≠ b * a := by
  rcases hGO.onan with ⟨-, hinv⟩ | ⟨hΩ, -⟩ | ⟨-, -, hinv⟩ | ⟨hk, hn, hX, hab⟩
  · exfalso
    rcases hirr _ hinv with h | h
    · exact hGO.fixSub_ne_bot h
    · apply hGO.commSub_ne_bot
      have h1 : commSub V Y ⊓ fixSub V Y = ⊥ := hGO.commSub_inf_fixSub'
      rwa [h, inf_top_eq] at h1
  · exfalso
    have hne : fixSub V Y ≠ commSub V Y := by
      intro h0
      apply hGO.fixSub_ne_bot
      have h1 : fixSub V Y ≤ commSub V Y ⊓ fixSub V Y := le_inf (h0 ▸ le_rfl) le_rfl
      rw [hGO.commSub_inf_fixSub'] at h1
      exact eq_bot_iff.2 h1
    have hidx : (MulAction.stabilizer X (fixSub V Y)).index = 2 := by
      rw [MulAction.index_stabilizer]
      change (omega V Y).ncard = 2
      rw [hΩ, Set.ncard_pair hne]
    exact hno _ (Subgroup.normal_of_index_eq_two hidx) hidx
  · exfalso
    rcases hirr _ hinv with h | h
    · exact hGO.commSub_ne_bot h
    · apply hGO.fixSub_ne_bot
      have h1 : commSub V Y ⊓ fixSub V Y = ⊥ := hGO.commSub_inf_fixSub'
      rwa [h, top_inf_eq] at h1
  · refine ⟨?_, ?_, hX, hab⟩
    · rw [hGO.card_V, hn]; norm_num
    · rw [hGO.card_fixSub, hk]; norm_num

end GOPair

end CFSG.GH74.Uniqueness.SU.SU2
