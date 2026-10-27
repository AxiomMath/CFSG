module

public import CFSG.ClassicalInvolution.Q3.TA3SOLDefs
public import CFSG.ClassicalInvolution.Q3.TA3SOLL3U3SL2
public import CFSG.GH74.Filter.Small.RankThree
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreRank

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg
open scoped MatrixGroups

section Classical

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {t : X}

theorem datum_three_le_twoRank_of_isClassicalSL2 (hD : TightDatum R S t) {F : Type} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) {L : Subgroup X}
    (hL : IsClassicalSL2 F L t) : 3 ≤ CFSG.Open.twoRank X := by
  obtain ⟨e⟩ := hL.nonempty_mulEquiv
  have : Group.IsPerfect L := isPerfect_of_equiv_sl2 h4 e
  obtain ⟨φ, hφ, hφL, hφt⟩ := exists_q8_of_mulEquiv_sl2 hodd L e
  have h1 : (⟨t, hL.mem⟩ : L) = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp (by rw [Subgroup.orderOf_mk, hL.orderOf_eq_two])
  exact datum_three_le_twoRank hD hL.le_centralizer φ hφ hφL
    (hφt.trans (congrArg Subtype.val h1.symm))

end Classical

theorem noDatumL3U3_holds : NoDatumL3U3 := by
  intro X _ _ _ tag p f htag hp hp2 h5 hm _ ⟨R, S, t, hD⟩
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  rcases htag with rfl | rfl
  · have hle := GH74.Filter.t_PSL_three_odd X p f hp2 hm
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
    have hoddK : Odd (Nat.card K) := by rw [hK]; exact hodd
    obtain ⟨L, hL⟩ := exists_isClassicalSL2_of_psl3 hoddK e hD.order
    have hge := datum_three_le_twoRank_of_isClassicalSL2 hD hoddK (by rw [hK]; omega) hL
    omega
  · have hle := GH74.Filter.t_PSU_three_odd X p f hp2 hm
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := ClassicalGroups.Unitary.charP_of_card_sq hK
    obtain ⟨L, hL⟩ := exists_isClassicalSL2_of_psu3 hK hp2 h5 e hD.order
    have hF := card_fixedSubfield hK
    have hge := datum_three_le_twoRank_of_isClassicalSL2 hD (by rw [hF]; exact hodd)
      (by rw [hF]; omega) hL
    omega

end CFSG.ClassicalInvolution.Q3.TA3
