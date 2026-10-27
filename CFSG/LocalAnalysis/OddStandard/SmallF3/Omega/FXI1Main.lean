module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXI1Model
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CBSwapFin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FStdChar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82FactI1Cent_holds : Asc82FactI1Cent := by
  unfold Asc82FactI1Cent
  intro G _ _ L hL s hs2 hsN hsC k hks h9
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hsgn, ⟨e⟩⟩ :=
    isOmegaStar_of_lieModel_psu (s7f_lieModel_center_of_twoU43 hL.1 hL.2)
  obtain ⟨x, hx⟩ := ff_exists_induces hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e hsN
  have hss : s * s = 1 := by rw [← sq, ← hs2]; exact pow_orderOf_eq_one s
  have hx2 : x * x = 1 := ff6m_induces_sq hQ (by omega) e hx hss
  have hx1 : x ≠ 1 := fun h =>
    hsC ((ff6m_centralizer_iff_eq_one hL.1 hQ (by omega) e hx).mpr h)
  have hfix : e (QuotientGroup.mk k) ∈ ffFix hQ (by omega) x := by
    refine mem_fixSub_iff.mpr ?_
    apply Subtype.ext
    rw [coe_ffSimOmegaAct]
    have hconj : (k : G) = s * k * s⁻¹ := by rw [← hks]; group
    exact (hx.2 k k hconj).symm
  have hord0 : orderOf (QuotientGroup.mk k : ↥L ⧸ Subgroup.center ↥L) ≠ 0 :=
    (orderOf_pos _).ne'
  have hord : orderOf (e (QuotientGroup.mk k)) = orderOf (QuotientGroup.mk k : ↥L ⧸
      Subgroup.center ↥L) := MulEquiv.orderOf_eq e _
  have hw9 : orderOf (e (QuotientGroup.mk k) ^ (orderOf (e (QuotientGroup.mk k)) / 9)) = 9 :=
    orderOf_pow_orderOf_div (by rw [hord]; exact hord0) (by rw [hord]; exact h9)
  obtain ⟨α, hα⟩ := fx_simHasType_one hQ hdim hsgn hx1 hx2 ((ffFix hQ (by omega) x).pow_mem hfix _)
    hw9
  exact ⟨α, V, i1, i2, i3, Q, hQ, e, x, hdim, hsgn, hx, hα⟩

end CFSG.OddStandard.SmallF3.Omega
