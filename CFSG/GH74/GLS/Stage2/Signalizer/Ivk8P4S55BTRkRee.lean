module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkG2Kind
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Ree
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Arith
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAutRank

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 RkG2


namespace RkRee

theorem ree_data {Y : Type} [Group Y] {f : ℕ} (hLie : LieModel Y .twistedG2 0 3 f) :
    ReeTitsModel Y .twistedG2 3 f ∧ Finite Y ∧ 9 ∣ Nat.card Y ∧ ∀ k : Kind, ¬ KindFactor k Y := by
  have hR : ReeTitsModel Y .twistedG2 3 f := by
    rcases hLie with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
    · exact absurd hh (by decide)
    · exact absurd hh (by decide)
    · exact hR
    · exact absurd hh (by decide)
  obtain ⟨a, ha, hfa, hfin, hcard⟩ := card_ree_model hR
  subst hfa
  refine ⟨hR, hfin, ?_, ree_bad_numbers ha hcard⟩
  rw [hcard]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
  rw [← pow_mul]
  show 3 ^ 2 ∣ _
  exact pow_dvd_pow 3 (by omega : 2 ≤ (2 * a + 1) * 3)

theorem center_eq_bot_of_nine_dvd {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (h9 : 9 ∣ Nat.card Y) : center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h0 | h0
  · exact h0
  · exfalso
    have hcomm : ∀ a b : Y, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top b) a
    let _ : CommGroup Y := { ‹Group Y› with mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := Y)
    rcases hp.eq_one_or_self_of_dvd 9 h9 with h | h
    · omega
    · rw [← h] at hp
      exact absurd hp (by norm_num)

end RkRee

open RkRee in
theorem rankCell_free : RankCell FRee := by
  intro k hk Y _ _ _ hY
  obtain ⟨f, -, hLie⟩ := hY
  obtain ⟨hR, -, h9, hbad⟩ := ree_data hLie
  refine ⟨not_kindFactorAll_of_not_kindFactor hk hbad, fun E hE _ => ?_⟩
  have := hE
  have h8 := CFSG.GH74.GLS.IVK.GHInv.card_le_two_pow_add_of_aut (center_eq_bot_of_nine_dvd h9)
    (CFSG.GH74.GLS.IVK.GHInv.ree_card_elementary_le hR)
    (CFSG.GH74.GLS.IVK.GHInv.ree_card_outer_elementary hR) E fun e he => by
      rw [← pow_two]
      exact elemPow_eq_one_of_isElementaryAbelian e he
  simpa using h8

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
