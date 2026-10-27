module

public import CFSG.LargeExtraspecial.S14NQBasic
public import CFSG.LargeExtraspecial.S14Five
public import CFSG.LargeExtraspecial.S14Nine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem eq_or_eq_of_rnOmega (hCE : CentralExtInput.{0}) (hSt : Stage S g t) {m e : ℕ}
    (hΩ : RNOmega S g t (2 * m)) (hcard : Nat.card (Nbar S g t) = 2 ^ (e + 1))
    (he : e = 2 ^ (m - 1) ∨ (¬ RNPlus S g t ∧ e = 2 ^ m)) {D : Subgroup S.O}
    (htD : zpowers t ≤ D) (hDN : D ≤ Nbar S g t)
    (hDR : ∀ r ∈ Rbar S g t, ∀ x ∈ D, r * x * r⁻¹ ∈ D) : D = zpowers t ∨ D = Nbar S g t := by
  obtain ⟨H, C, ht, ht1, hVQ, hΩc, hdim⟩ := hΩ
  have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
  obtain ⟨Dd⟩ := S8.Std.nonempty hCE hNo hΩc
  have hDm : Dd.m = m := by have := Dd.hdim; omega
  have : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ Dd.hgen Dd.hN0 Dd.hh Dd.hb
  have hRD := timmesfeld_6_5_omega H hNo C ht ht1 hVQ hΩc Dd.hN0 Dd.hh Dd.hb Dd.hX Dd.hE
  have htD' : t ∈ D := htD (mem_zpowers t)
  obtain ⟨hdvd, hdvd', -⟩ := S8.dvd_and_two_mul_of_invariant (nqRep S g t Dd.hX) Dd.hm Dd.hdim
    (aV_ne_zero H ht) Dd.hQa Dd.Q_bV Dd.polar_aV_bV hRD (N' := nqSub S g t D)
    (fun e' _ hv => nqRep_mem_nqSub Dd.hX htD' hDR e' hv)
  have hfin := finrank_NQ_of_card ht1 (mul_self_of_mem_Lbar S H.conj_mem ht)
    (self_mem_Nbar H ht) hcard
  refine eq_zpowers_or_eq_Nbar_of_dvd htD hDN ?_
  rw [hfin]
  rcases he with rfl | ⟨hp, rfl⟩
  · rw [← hDm]; exact hdvd
  · have hmin : Dd.IsMinus := by
      by_contra h
      exact hp ((rnPlus_iff_not_isMinus Dd).mpr h)
    rw [← hDm]
    exact hdvd' fun T _ hT => hmin T hT

theorem eq_or_eq_of_rnSp (hCE : CentralExtInput.{0}) (hSt : Stage S g t) {m : ℕ}
    (hSp : RNSp S g t (2 * m)) (hm : 1 ≤ m) (hcard : Nat.card (Nbar S g t) = 2 ^ (2 ^ m + 1))
    {D : Subgroup S.O} (htD : zpowers t ≤ D) (hDN : D ≤ Nbar S g t)
    (hDR : ∀ r ∈ Rbar S g t, ∀ x ∈ D, r * x * r⁻¹ ∈ D) : D = zpowers t ∨ D = Nbar S g t := by
  obtain ⟨H, C, ht, ht1, hVQ, hSpc, hdim⟩ := hSp
  have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSpc
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSpc
  have : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ hgen hN0 hh hb
  have hRD := timmesfeld_6_5_sp H hNo C ht ht1 hVQ hSpc hN0 hh hb
  have htD' : t ∈ D := htD (mem_zpowers t)
  have hdvd := S9.pow_dvd_finrank_of_invariant (nqRep S g t hSpc.eq_sp)
    (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ) hm hdim
    (beta_aV_bV H C ht ht1 hVQ hh hb) hRD (U := nqSub S g t D)
    (fun x _ hu => nqRep_mem_nqSub hSpc.eq_sp htD' hDR x hu)
  have hfin := finrank_NQ_of_card ht1 (mul_self_of_mem_Lbar S H.conj_mem ht)
    (self_mem_Nbar H ht) hcard
  refine eq_zpowers_or_eq_Nbar_of_dvd htD hDN ?_
  rw [hfin]
  exact hdvd

theorem nqIrredStmt_of (hCE : CentralExtInput.{0}) : NQIrredStmt := by
  intro G _ _ _ S g t c hSt hocc _ hc8 hc6 D htD hDN hDR
  obtain ⟨hh, -, hcard⟩ := hocc
  cases c with
  | omegaMinus8 =>
    exact eq_or_eq_of_rnOmega hCE hSt (m := 4) (e := 16) hh.1 hcard
      (Or.inr ⟨hh.2, rfl⟩) htD hDN hDR
  | omegaMinus6 =>
    exact eq_or_eq_of_rnOmega hCE hSt (m := 3) (e := 8) hh.1 hcard
      (Or.inr ⟨hh.2, rfl⟩) htD hDN hDR
  | omegaPlus12 =>
    exact eq_or_eq_of_rnOmega hCE hSt (m := 6) (e := 32) hh.1 hcard
      (Or.inl rfl) htD hDN hDR
  | omegaPlus10 =>
    exact eq_or_eq_of_rnOmega hCE hSt (m := 5) (e := 16) hh.1 hcard
      (Or.inl rfl) htD hDN hDR
  | omegaPlus8a =>
    exact eq_or_eq_of_rnOmega hCE hSt (m := 4) (e := 8) hh.1 hcard
      (Or.inl rfl) htD hDN hDR
  | omegaPlus8b => exact absurd rfl hc8
  | omegaPlus6 => exact absurd rfl hc6
  | sp6 => exact eq_or_eq_of_rnSp hCE hSt (m := 3) hh (by norm_num) hcard htD hDN hDR
  | sp8 => exact eq_or_eq_of_rnSp hCE hSt (m := 4) hh (by norm_num) hcard htD hDN hDR

end CFSG.LargeExtraspecial.S14
