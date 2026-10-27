module

public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Quot
public import CFSG.GH74.GLS.C3.Layer1.BkP85SpJ2

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85
  CFSG.GH74.GLS.Th2.P85.Sp CFSG.GH74.GLS.TwoThin
open CFSG.GH74.Generic.S45 CFSG.GH74.Generic.S45.EvSpor CFSG.Sporadic.Schreier

theorem b_thm2_p89_J2_of
    (hB : B_p810_J2) :
    B_thm2_p89_J2 := by
  intro G _ _ x y K T S M L hs hJ2 hLtop hgam _hc W hWsyl hWM hTW v hvW hv2 hvc hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsetup := hs.toP85Setup
  have hvM : v ∈ M := hWM hvW
  obtain ⟨eJ⟩ := hJ2
  let e : Mb M ≃* NativeSporadic.J2 :=
    ((MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv).symm.trans eJ
  have hQ2 : NativeSporadic.IsSporadic (Mb M) .J2 := ⟨e⟩
  have hF : J2Facts (imgM M L) := by
    exact J2Facts.of_equiv (eJ.trans j2PermEquiv) j2_facts
  have hcardM : Nat.card (Mb M) = 604800 := by
    rw [← Subgroup.card_top, ← hLtop]
    exact hF.card
  have hQM : T ⊓ CxK x K ≤ M := hsetup.hQ.le.trans inf_le_left
  have hQW : T ⊓ CxK x K ≤ W := fun q hq => hTW ⟨hq.1, hQM hq⟩
  have hQcent : ∀ q ∈ T ⊓ CxK x K, q ≠ 1 → centralizer ({q} : Set G) ≤ M := by
    intro q hq hq1
    have hq2 : q ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hs.Qelem.exponent_dvd_p ⟨q, hq⟩)
    have hqord : orderOf q = 2 := orderOf_eq_prime hq2 hq1
    exact (C3.Layer1.U1a.centralizer_le_gammaK (Q := T ⊓ CxK x K) hq hqord).trans hgam
  have hWsylM : IsSylowOf 2 W M := hWsyl.of_le hWM le_top
  have hWb : IsSylowOf 2 (imgM M W) ⊤ := by
    have := isSylowOf_imgM_of_le (le_refl M) hWsylM
    rwa [P89Std.imgM_top] at this
  have hWbcard : Nat.card ↥(imgM M W) = 2 ^ 7 := by
    rw [hWb.card_eq, Subgroup.card_top, hcardM, factorization_604800]
  have hvb2 : orderOf (barMk ↥M ⟨v, hvM⟩) = 2 :=
    orderOf_barMk ((Subgroup.orderOf_mk v hvM).trans hv2)
  have hWbC : imgM M W ≤ centralizer ({barMk ↥M ⟨v, hvM⟩} : Set (Mb M)) := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hw
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hvc _ hm).symm
  have h128 : 2 ^ 7 ∣ Nat.card ↥(centralizer ({barMk ↥M ⟨v, hvM⟩} : Set (Mb M))) := by
    rw [← hWbcard]
    exact Subgroup.card_dvd_of_le hWbC
  obtain ⟨Ebar, hfacts⟩ := C3.Layer1.Bk.J2C.j2_cent_facts hQ2 hvb2 h128
  have hstd : P89Std M W (T ⊓ CxK x K) v Ebar :=
    { W_syl := hWsyl, W_le := hWM, v_mem := hvW, v_two := hv2, v_cent := hvc,
      Q_le := hQW, Q_card := hs.Qcard, Q_elem := hs.Qelem, Q_cent := hQcent,
      Mb_card := hcardM, facts := hfacts }
  exact hstd.false_of_B_p810_J2 hB hsetup.hG hnot

end CFSG.GH74.GLS
