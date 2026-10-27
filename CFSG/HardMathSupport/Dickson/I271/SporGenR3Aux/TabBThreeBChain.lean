module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeBConfig
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeBLayer
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Blueprint CFSG.Open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
  CFSG.HardMathSupport.Solomon.Coordinator.B3B
open scoped Matrix

set_option linter.unusedSectionVars false

@[expose] def B3BComponentLeaf : Prop :=
  ∀ J : Subgroup NativeSporadic.B, CFSG.Open.IsQuasisimple ↥J →
    3 ∣ Nat.card (Subgroup.center ↥J) → ¬ 7 ∣ Nat.card J → 3 ^ 8 ∣ Nat.card (MulAut ↥J) → False

section Chain




theorem uninverted_isConj_phiB_t3_one
    {s : NativeSporadic.B} (hs : orderOf s = 3)
    (hunv : ∀ d : NativeSporadic.B, CFSG.Monster.GMS.BabyInv 0 d → d * s * d⁻¹ ≠ s⁻¹) :
    IsConj s (phiB (t3 1)) := by
  have hnot0 : ¬ IsConj s (phiB (t3 0)) := by
    intro hc
    obtain ⟨d, hd, hdr⟩ := phiB_t3_zero_inverted
    obtain ⟨c, hcx⟩ := isConj_iff.1 hc
    refine hunv (c⁻¹ * d * c) (CFSG.Monster.GMS.BabyInv.of_isConj hd
      (isConj_iff.2 ⟨c⁻¹, by simp⟩)) ?_
    have hx' : s = c⁻¹ * phiB (t3 0) * c := by rw [← hcx]; group
    calc c⁻¹ * d * c * s * (c⁻¹ * d * c)⁻¹
        = c⁻¹ * (d * phiB (t3 0) * d⁻¹) * c := by rw [hx']; group
      _ = s⁻¹ := by rw [hdr, hx']; group
  obtain ⟨i, hi⟩ := bThree_classes s hs
  fin_cases i
  · exact absurd hi hnot0
  · exact hi
  · exact absurd (hi.trans bThreeRc_holds) hnot0
  · exact hi.trans bThreeRd_holds

theorem b3b_noComp_of_leaf
    (hL : B3BComponentLeaf) :
    ∀ s : NativeSporadic.B, orderOf s = 3 →
      (∀ d : NativeSporadic.B, CFSG.Monster.GMS.BabyInv 0 d → d * s * d⁻¹ ≠ s⁻¹) →
      ∀ J : Subgroup NativeSporadic.B,
        ¬ GLAPComponent 3 (Subgroup.centralizer ({s} : Set NativeSporadic.B)) J := by
  intro s hs hunv J hJ
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨z, hz3, hzrk, ⟨P, hPC, hPcard, hPZ⟩, haut⟩ := exists_z_sylow_aut
  have hzc : IsConj z (phiB (t3 1)) := isConj_phiB_t3_one_of_rk hz3 hzrk
  have hsc : IsConj s (phiB (t3 1)) := uninverted_isConj_phiB_t3_one hs hunv
  obtain ⟨c, hc⟩ := isConj_iff.1 (hsc.trans hzc.symm)
  have hOs : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set NativeSporadic.B)) = ⊥ :=
    oPrimeCoreTrivialAt_B_three s hs
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_of_glaPComponent_of_comm
      Nat.prime_three hJ (fun g _ o ho => by
        rw [hOs, Subgroup.mem_bot] at ho
        rw [ho, one_mul, mul_one])
  have hJc : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({s} : Set NativeSporadic.B)) :=
    ⟨hJ.1, hJ.2.1, hJq⟩
  have hJz : CFSG.Open.IsComponentOf (J.map (MulAut.conj c).toMonoidHom)
      (Subgroup.centralizer ({z} : Set NativeSporadic.B)) := by
    have h := CFSG.HardMathSupport.Solomon.Coordinator.bmInv_isComponentOf_map (MulAut.conj c) hJc
    rwa [MulAut.conj_apply, hc] at h
  have hOz : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({z} : Set NativeSporadic.B)) = ⊥ :=
    oPrimeCoreTrivialAt_B_three z hz3
  have hzmem : z ∈ Subgroup.centralizer ({z} : Set NativeSporadic.B) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨J', hJ', h3⟩ := exists_isComponentOf_dvd_card_center Nat.prime_three hzmem
    (fun g hg => Subgroup.mem_centralizer_singleton_iff.1 hg) hz3 hPC hPcard hPZ hOz hJz
  have h9 : 9 ∣ (Subgroup.center ↥J').index := nine_dvd_index_center hJ'.2.2.1 h3
  have h7C : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({z} : Set NativeSporadic.B)) := by
    rw [CFSG.Monster.Existence.natCard_centralizer_eq_of_isConj hzc]
    exact bThreeB_seven_free
  exact hL J' hJ'.2.2 h3 (fun h => h7C (h.trans (Subgroup.card_dvd_of_le hJ'.1)))
    (haut J' hJ' h9)

end Chain

end CFSG.HardMathSupport.Dickson.I271
