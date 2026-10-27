module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HMono
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IOrd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem exists_conj_into_hPO (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) {t : OGroup Q}
    (ht : t ∈ normalizer (ffP0 hQ fr : Set (OGroup Q))) (h2 : t * t = 1) :
    ∃ n ∈ normalizer (ffP0 hQ fr : Set (OGroup Q)), n * t * n⁻¹ ∈ hPO fr := by
  classical
  let N : Subgroup (OGroup Q) := normalizer (ffP0 hQ fr : Set (OGroup Q))
  haveI : Finite (OGroup Q) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_oGroup_six_minus hQ hdim hsgn]; norm_num)
  have hPO2 : IsPGroup 2 (hPO fr) := IsPGroup.of_card (p := 2) (n := 10) (hPO_card fr)
  have hPOle : hPO fr ≤ N := hPO_le_normalizer hQ fr
  have hsylPO : IsSylow2Of (hPO fr) N := by
    refine ⟨hPOle, hPO2, ?_⟩
    intro hdvd
    obtain ⟨R, hRsyl, hleR⟩ := exists_isSylow2Of_ge hPO2 hPOle
    haveI : Finite R := Subtype.finite
    obtain ⟨m, hRm⟩ := hRsyl.2.1.exists_card_eq
    have hdvdR : 2 ^ m ∣ 2 ^ 10 * 25515 := by
      have h := R.card_subgroup_dvd_card
      rw [hRm, natCard_oGroup_six_minus hQ hdim hsgn,
        show 26127360 = 2 ^ 10 * 25515 by norm_num] at h
      exact h
    have hcop : Nat.Coprime (2 ^ m) 25515 :=
      (Nat.coprime_two_left.mpr (by decide : Odd 25515)).pow_left m
    have hmle : m ≤ 10 :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
        (hcop.dvd_of_dvd_mul_right hdvdR)
    have hcardR : Nat.card R ≤ Nat.card (hPO fr) := by
      rw [hRm, hPO_card fr]
      exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hmle
    have hR_eq : hPO fr = R := Subgroup.eq_of_le_of_card_ge hleR hcardR
    refine hRsyl.2.2 ?_
    rw [← hR_eq]
    exact hdvd
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact h2
  have hZ2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card_dvd_pow (p := 2) (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_iff_pow_eq_one.mpr ht2)
  have hZle : Subgroup.zpowers t ≤ N := Subgroup.zpowers_le.mpr ht
  obtain ⟨S, hSsyl, hZS⟩ := exists_isSylow2Of_ge hZ2 hZle
  obtain ⟨a, haN, ha⟩ := IsSylow2Of.exists_conj_mem hsylPO hSsyl
  have htS : t ∈ S := hZS (Subgroup.mem_zpowers t)
  have hconj : a⁻¹ * t * a ∈ hPO fr := (ha t).mp htS
  exact ⟨a⁻¹, N.inv_mem haN, by rwa [inv_inv]⟩

end CFSG.OddStandard.SmallF3.Omega
