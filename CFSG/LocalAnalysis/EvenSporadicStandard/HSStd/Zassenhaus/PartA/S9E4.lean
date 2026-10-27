module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9Harris
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Five
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9Pgl
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9Quot

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open
  CFSG.EvenSporadicStandard.HSStd

section

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA8.nonempty_five (hb : PAB G L t E W z) (a : PA8 L t E z) (hub : a.ub = t * a.u)
    (he4 : a.dcase = DCase.e4) :
    ∃ σ : Equiv.Perm (Fin 5), Nonempty (Five G t a.ub a.y σ) := by
  obtain ⟨σ, hσ, hι⟩ := a.ub_base
  have hσ2 : σ * σ = 1 := by
    obtain ⟨x, y, hxy, rfl⟩ := hσ
    exact Equiv.swap_mul_self x y
  have hcomm : a.ub * t = t * a.ub := PA5.comm_t_ub hb a.toPA7.toPA6.toPA5
  have hy3 : a.y * a.y * a.y = 1 := by
    have := pow_orderOf_eq_one a.y
    rwa [a.y_ord, pow_succ, pow_two] at this
  have hrange : a.ι.range = DE4 :=
    a.ι_range.resolve_left (fun h => by
      have := a.dcase_iff.2 h
      rw [he4] at this
      exact DCase.noConfusion this)
  obtain ⟨hu2, hu1⟩ := PA8.u_sq_twisted hb a hub
  refine ⟨σ, ⟨{ tu := hcomm.symm
                t_sq := hb.t_mul_t
                u_sq := mul_self_eq_one_of_orderOf_eq_two_fullness a.ub_ord
                T_ne := ?_
                y_cube := hy3
                ty := mem_Cen.1 a.t_cy
                uy := mem_Cen.1 a.ub_cy
                σ_sq := hσ2
                ι := a.ι
                ι_inj := a.ι_inj
                ι_t := a.ι_t
                ι_u := hι
                ι_range := hrange }⟩⟩
  rw [hub, ← mul_assoc, hb.t_mul_t, one_mul]
  exact hu1

theorem e4_quot_hs (hHiS : Harris311HiS) (hb : PAB G L t E W z) (a : PA8 L t E z)
    (hub : a.ub = t * a.u) (he4 : a.dcase = DCase.e4) :
    Nonempty (QuotT a.u ≃* NativeSporadic.HS) := by
  obtain ⟨hu2, hu1⟩ := PA8.u_sq_twisted hb a hub
  have hordu : orderOf a.u = 2 := orderOf_eq_two_of_sq hu2 hu1
  have hTu : t * a.ub = a.u := by rw [hub, ← mul_assoc, hb.t_mul_t, one_mul]
  have hT2 : orderOf (t * a.ub) = 2 := by rw [hTu]; exact hordu
  have h1 : fusionOddCore (QuotT (t * a.ub)) = ⊥ := fusionOddCore_quotT hb hT2
  have h2 : H2Prop (QuotT (t * a.ub)) := by
    let a0 : PA0 L t E z := a.toPA7.toPA6.toPA5.toPA4.toPA3.toPA2.toPA0
    let S := PA0.fusionSetup hb a0
    have hn : ¬ IsConj t (t * a0.u) := by
      have := a.ub_nconj
      rw [hub] at this
      exact this
    have hex := exists_mulEquiv_cent_u S hn a0.eAbar
    refine H2Prop.transport hTu.symm ⟨tBarU S, ?_, hex⟩
    have hne : tBarU S ≠ 1 := by
      intro h
      apply tBarU_not_mem_range S 1
      rw [map_one, h]
    exact orderOf_eq_two_of_sq (tBarU_sq S) hne
  have hK : CFSG.SectionRank.IsKGroupCat (QuotT (t * a.ub)) :=
    (hb.setting.1.isKGroupCat_centralizer_of_orderOf (n := 2) (by norm_num) hT2).quotient _
  have h3 : H3Prop (QuotT (t * a.ub)) := by
    obtain ⟨σ, ⟨F⟩⟩ := PA8.nonempty_five hb a hub he4
    have hS := five_nonempty_mulEquiv F
    have hg3 : (mkT (t * a.ub) F.yH) ^ 3 = 1 := by
      rw [← map_pow]
      have : F.yH ^ 3 = 1 := Subtype.ext (by
        change a.y ^ 3 = 1
        rw [pow_succ, pow_two]; exact F.y_cube)
      rw [this, map_one]
    have hcard : 120 < Nat.card (QuotT (t * a.ub)) := by
      have hTT : (t * a.ub) * (t * a.ub) = 1 := by rw [hTu]; exact hu2
      have hT1 : t * a.ub ≠ 1 := by rw [hTu]; exact hu1
      have h4 := card_quotT_mul_two hTT hT1
      have h5 : Nat.card ↥(Cen (t * a.ub)) ≥ 2880 := by
        rw [hTu]
        have := Subgroup.card_le_of_le (inf_le_right : (L ⊓ Cen a.u) ≤ Cen a.u)
        rw [a.card_Lu] at this
        exact this
      omega
    have hg1 : mkT (t * a.ub) F.yH ≠ 1 := by
      intro h
      have hy1 : F.yBar = 1 := by rw [Five.yBar, h, map_one]
      rw [hy1] at hS
      exact autCentralizer_not_five_of_one h1 hcard hS
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine ⟨mkT (t * a.ub) F.yH, orderOf_eq_prime hg3 hg1, ?_⟩
    exact five_nonempty_mulEquiv_centralizer F
  exact nonempty_quotT_transport hTu (harris_of_props hHiS hK h1 h2 h3)

end

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
