module

import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

@[expose] def cardGL8 : ℕ := 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127

theorem card_mulAut_dvd_cardGL8 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W ≤ 2 ^ 8) : Nat.card (MulAut W) ∣ cardGL8 := by
  have hW2 : IsPGroup 2 W := fun w => ⟨1, by simpa using hW w⟩
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hn8 : n ≤ 8 := by
    by_contra h
    have : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm a b) (fun a => hW a) hn
  have hGL : Nat.card (MulAut W) = Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :=
    Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toEquiv
  rw [hGL, Matrix.card_GL_field]
  interval_cases n <;>
    norm_num [cardGL8, Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]

theorem card_dvd_cardGL8 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W ≤ 2 ^ 8) {L : Type*} [Group L] [Finite L] (ρ : L →* MulAut W)
    (hρ : Function.Injective ρ) : Nat.card L ∣ cardGL8 := by
  exact (Subgroup.card_dvd_of_injective ρ hρ).trans (card_mulAut_dvd_cardGL8 hW hcard)

theorem not_dvd_cardGL8 : ¬ 13 ∣ cardGL8 ∧ ¬ 11 ∣ cardGL8 ∧ ¬ 5 ^ 3 ∣ cardGL8 := by
  unfold cardGL8
  norm_num

end CFSG.CGT.PushingUpLit.CGT6M
