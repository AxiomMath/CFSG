module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsM12
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalFactor
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverLift

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.External

theorem sporadicCoverRankInput_J2 :
    SporadicCoverRankInput .J2 := by
  intro Q _ _ hQ hZ2 ⟨e⟩
  obtain ⟨t, htZ, ht2, hcen⟩ := exists_center_eq_zpowers hZ2
  let e' : Q ⧸ center Q ≃* P := (e : Q ⧸ center Q ≃* NativeSporadic.J2).trans nativeEquivP
  set π : Q →* P := e'.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hπ
  have hπs : Function.Surjective π := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = zpowers t := (ker_quotientMap e').trans hcen
  have hQa : CFSG.Assembly.IsQuasisimple Q :=
    ((Foundations.SteinbergCA.quasisimple_iff Q).2.1).mp hQ
  obtain ⟨-, hlift, -⟩ := j2_double_cover_involution_lift_orders_fixCount hQa ht2 hcen π hπs hker
  have hR4 := orderOf_elemR
  have hS2 := orderOf_elemS
  have hw2 : orderOf (elemR ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd two_ne_zero (by rw [hR4]; norm_num), hR4]
  have hww : elemR ^ 2 * elemR ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (elemR ^ 2)
    rwa [hw2, pow_two] at h
  have hss : elemS * elemS = 1 := by rw [← pow_two, ← hS2, pow_orderOf_eq_one]
  have hconj : elemS * elemR ^ 2 * elemS⁻¹ = elemR ^ 2 := by
    rw [← conj_pow, elemS_conj_elemR, inv_pow]
    exact inv_eq_of_mul_eq_one_right hww
  have hcomm : elemS * elemR ^ 2 = elemR ^ 2 * elemS := mul_inv_eq_iff_eq_mul.mp hconj
  have hne : elemS ≠ elemR ^ 2 := by
    intro h
    have h1 : elemS * elemR * elemS⁻¹ = elemR := by
      rw [h]
      group
    rw [elemS_conj_elemR] at h1
    have h2 : elemR ^ 2 = 1 := by rw [pow_two]; nth_rw 1 [← h1]; exact inv_mul_cancel _
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hR4] at this
    omega
  have hsw2 : orderOf (elemS * elemR ^ 2) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, mul_assoc, ← mul_assoc (elemR ^ 2), ← hcomm, mul_assoc, hww, mul_one, hss]
    · intro h
      apply hne
      have h1 := eq_inv_of_mul_eq_one_left h
      rwa [inv_eq_of_mul_eq_one_right hww] at h1
  have hsD : elemS ∈ fixD := elemS_mem
  have hwD : elemR ^ 2 ∈ fixD := pow_mem elemR_mem 2
  have hswD : elemS * elemR ^ 2 ∈ fixD := mul_mem hsD hwD
  obtain ⟨a, ha⟩ := hπs elemS
  obtain ⟨b, hb⟩ := hπs (elemR ^ 2)
  have ha2 : orderOf a = 2 := hlift a (by rw [ha]; exact hS2)
    (by rw [ha]; exact fixCount_of_mem_fixD hsD hS2)
  have hb2 : orderOf b = 2 := hlift b (by rw [hb]; exact hw2)
    (by rw [hb]; exact fixCount_of_mem_fixD hwD hw2)
  have hab2 : orderOf (a * b) = 2 := hlift (a * b) (by rw [map_mul, ha, hb]; exact hsw2)
    (by rw [map_mul, ha, hb]; exact fixCount_of_mem_fixD hswD hsw2)
  have hsq : ∀ {x : Q}, orderOf x = 2 → x * x = 1 := fun hx => by
    rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hab : a * b = b * a := by
    have h1 := hsq hab2
    have h2 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [h2, mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq hb2),
      inv_eq_of_mul_eq_one_right (hsq ha2)]
  have ht1 : t ≠ 1 := by rintro rfl; rw [orderOf_one] at ht2; omega
  have hne1 : ∀ {x : P}, orderOf x = 2 → x ≠ 1 := fun hx h => by
    rw [h, orderOf_one] at hx; omega
  refine three_le_pRank_of_four_group (τ := MonoidHom.id Q) (πG := π) (πQ := π) (fun _ => rfl)
    (hsq ha2) (hsq hb2) hab (by rw [ha]; exact hne1 hS2) (by rw [hb]; exact hne1 hw2)
    (by rw [map_mul, ha, hb]; exact hne1 hsw2) htZ (hsq ht2) ht1
    (by rw [← MonoidHom.mem_ker, hker]; exact mem_zpowers t)

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
