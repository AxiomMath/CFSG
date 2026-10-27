module

public import CFSG.HardMathSupport.Dickson.BMRows.M11Sylow
public import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRows

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Monster CFSG.Monster.B CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Rep4371 CFSG.Monster.Existence CFSG.Monster.Griess
  CFSG.AGLEmbedding.Norton.Gen11 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven
open CFSG.LocalAnalysis.GLTheoremA

section Eleven


private theorem factorization_card_Gmat_eleven : (Nat.card Gmat).factorization 11 = 2 := by
  have h : CFSG.Open.monsterOrder =
      11 ^ 2 * 6677829956979445255259999214559593033105408000000000 := by
    norm_num [CFSG.Open.monsterOrder]
  rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, h,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem not_two_pow_seven_dvd_card_centralizer_eleven {k : Gmat} (hk : orderOf k = 11) :
    ¬ 2 ^ 7 ∣ Nat.card (Subgroup.centralizer ({k} : Set Gmat)) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨hx, hy, hxy, hx1, h3, h4, -, -⟩ := eleven_gw_facts
  have hy3 := eleven_data_facts.1
  have hrot := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.eleven_rot_fact
    Certificates.certificate41508
  have hc : Commute (gw gen11W0) (gw gen11W1) := hxy
  obtain ⟨g, j, hgj⟩ := exists_conj_pow_of_eleven_lines (x₃ := gw gen11W2) (x₄ := gw gen11W3) hx hy
    hxy (by rw [h3, mul_inv_cancel_right, ((hc.pow_pow 6 3).symm).eq])
    (by rw [hy3, mul_inv_cancel_right]) (by rw [h4, mul_inv_cancel_right])
    (by rw [hrot, mul_inv_cancel_right]) hx1 factorization_card_Gmat_eleven hk
  have hj1 : gw gen11W0 ^ j ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hgj
    rw [hgj, orderOf_one] at hk
    norm_num at hk
  rw [hgj, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq,
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq_of_prime orderOf_x11 hj1]
  exact M11.not_two_pow_seven_dvd_card_centralizer_x11

theorem acompOK_gmat_eleven {k : Gmat} (hk : orderOf k = 11) : I1415Rows.ACompOK 11 k :=
  I1415Rows.acompOK_of_not_dvd_card (by norm_num) hk fun h =>
    not_two_pow_seven_dvd_card_centralizer_eleven hk
      ((show 2 ^ 7 ∣ 11 * 1814400 by norm_num).trans h)

end Eleven

section Row


theorem i1415Row_M_eleven : I1415Rows.I1415Row .M 11 := by
  haveI : IsSimpleGroup Gmat := generated_rational_group_finite_simple.2.1
  obtain ⟨b⟩ : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  exact I1415Rows.arow_of_model sporadicOuterLeTwo_holds b ⟨_, _, w0_e0_ne⟩
    fun k hk => acompOK_gmat_eleven hk

end Row

end CFSG.HardMathSupport.Dickson.BMRows
