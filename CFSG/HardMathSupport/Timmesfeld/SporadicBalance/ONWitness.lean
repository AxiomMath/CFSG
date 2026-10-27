module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.TwoFive
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.RankThree.Native.ONThreeCentralizer
public import CFSG.RankThree.Native.ONThreeFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.ONAut
public import Certificates.Certificate13606
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.RankThree.Native CFSG.ONSchreier CFSG.ONSchreier.Native
open CFSG.Sporadic.ON.Native

theorem onThreeWitness_of_certificate :
    ∃ u g : Equiv.Perm (Fin N), u ∈ onThreeK ∧ orderOf u = 5 ∧ g ∈ onThreeK ∧
      g * u * g⁻¹ ∉ Subgroup.zpowers u := by
  have h := Certificates.certificate13606
  unfold Native.onWitnessChecks Native.onWitnessCore at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h5, h1⟩, hk⟩ := h
  have r1 := prep_onThreeY (j := 0) (by decide)
  have r2 := prep_onThreeY (j := 1) (by decide)
  set y1 := evalS onThreeY[0]! with hy1
  set y2 := evalS onThreeY[1]! with hy2
  have rU : PRep N (onSevenPow (pcomp nPts onThreeYArrs[0]! onThreeYArrs[1]!) 3) ((y1 * y2) ^ 3) :=
    prep_onSevenPow (prep_pcomp r1 r2) 3
  set u := (y1 * y2) ^ 3 with hu
  have hU5 : u ^ 5 = 1 :=
    (peq_iff (prep_onSevenPow rU 5) (prep_pid (n := N))).1 h5
  have hU1 : u ≠ 1 := by
    intro hU
    have h1' : peq nPts (onSevenPow (pcomp nPts onThreeYArrs[0]! onThreeYArrs[1]!) 3)
        (pid nPts) = true := (peq_iff rU (prep_pid (n := N))).2 hU
    rw [h1'] at h1
    exact absurd h1 (by decide)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf u = 5 := orderOf_eq_prime hU5 hU1
  have hm1 : y1 ∈ onThreeK := onThreeY_mem (j := 0) (by decide)
  have hm2 : y2 ∈ onThreeK := onThreeY_mem (j := 1) (by decide)
  have hmem : u ∈ onThreeK := pow_mem (mul_mem hm1 hm2) 3
  refine ⟨u, y1, hmem, hord, hm1, fun hz => ?_⟩
  obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hmod : u ^ k = u ^ (k % 5).toNat := by
    have h := zpow_eq_zpow_emod' (x := u) k hU5
    have h0 : 0 ≤ k % 5 := Int.emod_nonneg _ (by norm_num)
    have hjk : (k % (5 : ℕ) : ℤ) = (((k % 5).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0]; norm_num
    rw [h, hjk, zpow_natCast]
  obtain ⟨j, hjdef⟩ : ∃ j, j = (k % 5).toNat := ⟨_, rfl⟩
  have hj5 : j < 5 := by omega
  rw [← hjdef] at hmod
  have hgu : y1 * u = u ^ j * y1 := by
    have : u ^ j = y1 * u * y1⁻¹ := hmod.symm.trans hk'
    rw [this]; group
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · apply hU1
    simpa using hgu
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hk4 := allBelowN_spec hk (show j' < 4 by omega)
    have hpe : peq nPts (pcomp nPts onThreeYArrs[0]!
        (onSevenPow (pcomp nPts onThreeYArrs[0]! onThreeYArrs[1]!) 3))
        (pcomp nPts (onSevenPow (onSevenPow (pcomp nPts onThreeYArrs[0]! onThreeYArrs[1]!) 3)
          (j' + 1)) onThreeYArrs[0]!) = true :=
      (peq_iff (prep_pcomp r1 rU) (prep_pcomp (prep_onSevenPow rU (j' + 1)) r1)).2 hgu
    rw [hpe] at hk4
    exact absurd hk4 (by decide)

theorem gLAPPrimeCoreOf_centralizer_onThreeP :
    CFSG.Open.GLAPPrimeCoreOf 3 (Subgroup.centralizer ({onThreeP} : Set Pv)) = ⊥ := by
  have hC : Nat.card (Subgroup.centralizer ({onThreeP} : Set Pv)) = 3 ^ 4 * 40 := by
    rw [card_centralizer_eq_inf_of_mulEquiv (MulEquiv.refl Pv) onThreeP]
    exact card_centralizer_onThreeT
  refine gLAPPrimeCoreOf_eq_bot_of_card_forty (a := 4) (by norm_num) hC ?_ ?_
  · intro w hw Q hQ hle
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [CFSG.EvenSporadicStandard.Solomon78.pv_card_centralizer w hw] at hdvd
    have := card_le_of_isPGroup_of_dvd Nat.prime_three hQ (e := 2) (by norm_num) hdvd
    exact lt_of_le_of_lt this (by norm_num)
  · obtain ⟨u, g, hu, hu5, hg, hgu⟩ := onThreeWitness_of_certificate
    have hcent : ∀ (x : Equiv.Perm (Fin N)) (hx : x ∈ onThreeK),
        (⟨x, hx.2⟩ : Pv) ∈ Subgroup.centralizer ({onThreeP} : Set Pv) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hx.1)
    refine not_normal_five_of_witness hC (hcent u hu) ?_ (hcent g hg) ?_
    · rw [Subgroup.orderOf_mk]
      exact hu5
    · rintro ⟨k, hk⟩
      apply hgu
      refine ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this

theorem oPrimeCoreTrivialAt_Pv :
    OPrimeCoreTrivialAt 3 Pv := by
  intro y hy
  have hy' : orderOf (onEquivPv.symm y) = 3 := by rw [MulEquiv.orderOf_eq]; exact hy
  have ht : orderOf (onEquivPv.symm onThreeP) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_onThreeT
  obtain ⟨k, hk⟩ := onThree_fusion ht hy'
  have hk' : onEquivPv k * onThreeP * (onEquivPv k)⁻¹ = y := by
    have h := congrArg onEquivPv hk
    rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
  rw [← hk']
  exact (gLAPPrimeCoreOf_centralizer_conj _ onThreeP).2 gLAPPrimeCoreOf_centralizer_onThreeP

theorem sporadicOPrimeHolds_ONan_three :
    SporadicOPrimeHolds .ONan 3 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.ON := e
  exact OPrimeCoreTrivialAt.of_mulEquiv (e0.trans onEquivPv) oPrimeCoreTrivialAt_Pv

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
