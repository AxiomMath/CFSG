module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalEightOuter
import CFSG.ClassicalInvolution.Orders.Orthogonal
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedDerivedReindexEquiv statedDerivedReindexEquiv_symm_val)
open scoped Pointwise

theorem card_outer_dvd_of_pOmegaPlus (T : Type) [Group T] {n p f : ℕ}
    (h : StatedClassicalModel T .POmegaPlus n p f) :
    Nat.card (Outer T) ∣ Nat.gcd 4 ((p ^ f) ^ n - 1) * f * (if n = 4 then 6 else 2) := by
  have h0 := h
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  have hnle : 4 ≤ n := hn
  have hout : Nat.card (Outer T) =
      Nat.card (Outer (matrixProjectiveDerived (coordinateQuadPlus n K))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (coordinatePlusWitnessEquiv K e)).toEquiv
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
    (.inr (.inl rfl)) n p f h K hK (quadPlus n K) (coe_quadPlus n K) e
  set Qc := coordinateQuadPlus n K with hQc
  have hQ : ∃ v, Qc v ≠ 0 :=
    exists_nonzero_value Qc (by rw [hQc]; exact (coordinate_model_intrinsic_plus h K hK e).1)
  have hAbEq : Nat.card (Abelianization (matrixIsometries Qc)) =
      Nat.card (Abelianization (TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))) :=
    card_abelianization_matrixIsometries_reindex (plusIndexEquiv n) (quadPlus n K)
  obtain ⟨j, hj⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
      (plusIndexEquiv n) (quadPlus n K) hab
  have hj' : Nat.card (Abelianization (matrixIsometries Qc)) = 2 ^ j := hj
  have ha_raw : (inner (matrixProjectiveDerived Qc)).relIndex
      (isometryConjugationHom Qc).range ∣ Nat.card (Abelianization (matrixIsometries Qc)) :=
    relIndex_inner_dvd Qc
  have hcard_ab_le4 : Nat.card (Abelianization (matrixIsometries Qc)) ≤ 4 := by
    rw [hAbEq]
    by_cases hp2 : p = 2
    · exact (hab.2.2 hp2).trans (by norm_num)
    · exact hab.2.1 hp2
  have hcard_ab_le2 : p = 2 → Nat.card (Abelianization (matrixIsometries Qc)) ≤ 2 := by
    intro hp2
    rw [hAbEq]
    exact hab.2.2 hp2
  have ha_dvd_pow : (inner (matrixProjectiveDerived Qc)).relIndex
      (isometryConjugationHom Qc).range ∣ 2 ^ j := by
    rw [← hj']
    exact ha_raw
  set a := (inner (matrixProjectiveDerived Qc)).relIndex (isometryConjugationHom Qc).range
    with ha
  set b := (isometryConjugationHom Qc).range.relIndex (linearConjugationHom Qc).range
    with hb
  set c := (linearConjugationHom Qc).range.relIndex (matrixProjectiveImage Qc) with hc
  set k := (matrixProjectiveImage Qc).index with hk
  have houter : Nat.card (Outer T) = a * b * c * k := by
    rw [hout, card_outer_eq Qc]
  rw [houter]
  have ha_dvd4 : a ∣ 4 := by
    have hjle : j ≤ 2 := by
      apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      calc 2 ^ j = Nat.card (Abelianization (matrixIsometries Qc)) := hj'.symm
        _ ≤ 4 := hcard_ab_le4
    exact ha_dvd_pow.trans (pow_dvd_pow 2 hjle)
  have ha_dvd2 : p = 2 → a ∣ 2 := by
    intro hp2
    have hjle : j ≤ 1 := by
      apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      calc 2 ^ j = Nat.card (Abelianization (matrixIsometries Qc)) := hj'.symm
        _ ≤ 2 := hcard_ab_le2 hp2
    exact ha_dvd_pow.trans (pow_dvd_pow 2 hjle)
  have hb_dvd_gcd : b ∣ Nat.gcd (Nat.card K - 1) 2 := by
    have h := relIndex_isometryRange_dvd Qc hQ
    have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = Nat.gcd (Nat.card K - 1) 2 := by
      rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
    rwa [hsq] at h
  have hb_dvd2 : b ∣ 2 :=
    hb_dvd_gcd.trans (Nat.gcd_dvd_right _ _)
  have hb_eq_one : p = 2 → b = 1 := by
    intro hp2
    have hodd : Odd (((2 : ℕ) ^ f) - 1) :=
      Nat.Even.sub_odd (Nat.one_le_pow f 2 (by norm_num))
        (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    have hgcd : Nat.gcd (Nat.card K - 1) 2 = 1 := by
      rw [hK, hp2]
      exact Nat.coprime_two_right.mpr hodd
    rw [hgcd] at hb_dvd_gcd
    exact Nat.dvd_one.mp hb_dvd_gcd
  have hc_dvd : c ∣ f := by
    have h := relIndex_linearRange_dvd Qc
    exact h.trans ((Subgroup.card_subgroup_dvd_card
      (fieldProjection Qc).range).trans (card_ringAut_and_isCyclic hp K hK).1.dvd)
  have hk_one : 5 ≤ n → k = 1 := by
    intro h5
    have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
      (.inr (.inl rfl)) n p f h) K hK e).1
    have horbit := orthogonal_geometry_plus_point_family_orbit h hK e
    rw [hk, ← hEA, horbit.2.2.2.2.1 h5, Subgroup.index_top]
  have hk_three : n = 4 → k = 1 ∨ k = 3 := by
    intro h4
    subst h4
    exact index_matrixProjectiveImage_plus_four h K hK e
  have hk_dvd : n = 4 → k ∣ 3 := by
    intro h4
    rcases hk_three h4 with h1 | h1
    · rw [h1]
      norm_num
    · rw [h1]
  by_cases hp2 : p = 2
  · have hG : Nat.gcd 4 ((p ^ f) ^ n - 1) = 1 := by
      subst hp2
      have heven : Even (((2 : ℕ) ^ f) ^ n) := by
        rw [← pow_mul]
        exact Nat.even_pow.mpr ⟨even_two, Nat.mul_ne_zero (by omega) (by omega)⟩
      have hodd : Odd (((2 : ℕ) ^ f) ^ n - 1) :=
        Nat.Even.sub_odd (Nat.one_le_pow n (2 ^ f) (by norm_num)) heven odd_one
      have hmod : (((2 : ℕ) ^ f) ^ n - 1) % 4 = 1 ∨
          (((2 : ℕ) ^ f) ^ n - 1) % 4 = 3 := by
        have := Nat.odd_iff.mp hodd
        omega
      rcases hmod with h | h
      · rw [Nat.gcd_rec, h]
        norm_num
      · rw [Nat.gcd_rec, h]
        norm_num
    have hb1 : b = 1 := hb_eq_one hp2
    have ha2 : a ∣ 2 := ha_dvd2 hp2
    rw [hG, hb1]
    by_cases hn4 : n = 4
    · subst hn4
      rw [if_pos rfl]
      have hkd : k ∣ 3 := hk_dvd rfl
      have hdiv : a * 1 * c * k ∣ 2 * 1 * f * 3 :=
        mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ha2 dvd_rfl) hc_dvd) hkd
      rw [show (1 : ℕ) * f * 6 = 2 * 1 * f * 3 by ring]
      exact hdiv
    · have hk1 : k = 1 := hk_one (by omega)
      rw [if_neg hn4, hk1]
      have hdiv : a * 1 * c * 1 ∣ 2 * 1 * f * 1 :=
        mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ha2 dvd_rfl) hc_dvd) dvd_rfl
      rw [show (1 : ℕ) * f * 2 = 2 * 1 * f * 1 by ring]
      exact hdiv
  · have hchar := ringChar_eq_of_card_eq hp hf hK
    have h2 : (2 : K) ≠ 0 := by
      rw [Ne, two_eq_zero_iff_ringChar_eq_two (hchar ▸ hp), hchar]
      exact hp2
    have hn3 : 3 ≤ n := by omega
    have hneg : ¬ IsSquare ((-1 : K) ^ n) →
        (⟨-1, neg_one_mem_matrixIsometries Qc⟩ : matrixIsometries Qc) ∉
          commutator (matrixIsometries Qc) := by
      intro hns hmem
      have hD : (-1 : GL (Fin (2 * n)) K) ∈ matrixDerived Qc := by
        rw [matrixDerived_eq_map_commutator]
        exact ⟨_, hmem, rfl⟩
      have hval := statedDerivedReindexEquiv_symm_val (plusIndexEquiv n) (quadPlus n K)
        (coe_quadPlus n K) ⟨-1, hD⟩
      have hm1 : (reindexMatrixEquiv (plusIndexEquiv n)).symm
          (-1 : GL (Fin (2 * n)) K) = -1 := by
        rw [MulEquiv.symm_apply_eq]
        ext i j
        simp [reindexMatrixEquiv_val, Matrix.neg_apply, Matrix.one_apply]
      have hO := ((statedDerivedReindexEquiv (plusIndexEquiv n) (quadPlus n K)
        (coe_quadPlus n K)).symm ⟨-1, hD⟩).property
      rw [hval, hm1] at hO
      have e1 : toLinEquiv (Fin n ⊕ Fin n) K (-1) = LinearEquiv.neg K := by
        refine LinearEquiv.ext fun x => ?_
        rw [toLinEquiv_apply, Units.val_neg, Units.val_one, neg_mulVec, one_mulVec]
        rfl
      rw [statedOmega_eq_map_elementaryGroup (coe_quadPlus n K)
        (commutator_orthogonalGroup_quadPlus hn3), Subgroup.mem_map_equiv,
        MulEquiv.symm_symm, e1] at hO
      exact hns ((CFSG.ClassicalInvolution.neg_mem_elementaryGroup_quadPlus_iff h2 hn3).mp hO)
    have ha_dvd2' : ¬ IsSquare ((-1 : K) ^ n) → a ∣ 2 := by
      intro hns
      have h2a : 2 * a ≤ Nat.card (Abelianization (matrixIsometries Qc)) := by
        rw [ha]
        exact two_mul_relIndex_inner_le Qc (hneg hns)
      have hle : a ≤ 2 := by omega
      obtain ⟨i, -, hai⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ha_dvd_pow
      have hi : i ≤ 1 := by
        apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
        calc 2 ^ i = a := hai.symm
          _ ≤ 2 := hle
      rw [hai]
      exact pow_dvd_pow 2 hi
    have hpodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    rcases CFSG.ClassicalInvolution.odd_pow_mod_four hpodd n with hmod | hmod
    · have hG : Nat.gcd 4 ((p ^ f) ^ n - 1) = 4 := by
        apply CFSG.ClassicalInvolution.gcd_four_of_mod_zero
        have h1 : 1 ≤ (p ^ f) ^ n := Nat.one_le_pow n (p ^ f) (pow_pos hp.pos f)
        omega
      rw [hG]
      by_cases hn4 : n = 4
      · subst hn4
        rw [if_pos rfl]
        have hkd : k ∣ 3 := hk_dvd rfl
        have hdiv : a * b * c * k ∣ 4 * 2 * f * 3 :=
          mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ha_dvd4 hb_dvd2) hc_dvd) hkd
        rw [show (4 : ℕ) * f * 6 = 4 * 2 * f * 3 by ring]
        exact hdiv
      · have hk1 : k = 1 := hk_one (by omega)
        rw [if_neg hn4, hk1]
        have hdiv : a * b * c * 1 ∣ 4 * 2 * f * 1 :=
          mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ha_dvd4 hb_dvd2) hc_dvd) dvd_rfl
        rw [show (4 : ℕ) * f * 2 = 4 * 2 * f * 1 by ring]
        exact hdiv
    · have hns : ¬ IsSquare ((-1 : K) ^ n) := by
        intro hsq
        have h1 := (CFSG.ClassicalInvolution.isSquare_neg_one_pow_iff hK hpodd n).mp hsq
        omega
      have ha2 : a ∣ 2 := ha_dvd2' hns
      have hG : Nat.gcd 4 ((p ^ f) ^ n - 1) = 2 := by
        apply CFSG.ClassicalInvolution.gcd_four_of_mod_two
        have h1 : 1 ≤ (p ^ f) ^ n := Nat.one_le_pow n (p ^ f) (pow_pos hp.pos f)
        omega
      have hn4 : n ≠ 4 := by
        rintro rfl
        have h4 : (p ^ f) ^ 4 % 4 = 1 :=
          CFSG.ClassicalInvolution.pow_mod_four_of_even hpodd (by decide : Even 4)
        omega
      have hk1 : k = 1 := hk_one (by omega)
      rw [hG, if_neg hn4, hk1]
      have hdiv : a * b * c * 1 ∣ 2 * 2 * f * 1 :=
        mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ha2 hb_dvd2) hc_dvd) dvd_rfl
      rw [show (2 : ℕ) * f * 2 = 2 * 2 * f * 1 by ring]
      exact hdiv

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

end
