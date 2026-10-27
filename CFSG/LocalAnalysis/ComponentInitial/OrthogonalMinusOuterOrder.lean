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
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedDerivedReindexEquiv statedDerivedReindexEquiv_symm_val)
open CFSG.Open
open scoped Pointwise

theorem card_outer_dvd_of_pOmegaMinus (T : Type) [Group T] {n p f : ℕ}
    (h : StatedClassicalModel T .POmegaMinus n p f) :
    Nat.card (Outer T) ∣ Nat.gcd 4 ((p ^ f) ^ n + 1) * f * 2 := by
  have h0 := h
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
  change 4 ≤ n at hn
  have hn1 : 1 ≤ n := by omega
  set Qc := coordinateQuadMinus n K hn1 b c with hQc
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaMinus
    (.inr (.inr rfl)) n p f h0 K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hE : matrixProjectiveImage Qc = ⊤ := by
    rw [hQc]
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaMinus
      (.inr (.inr rfl)) n p f h0) hn1 K hK b c hirr e).1]
    exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T
      .POmegaMinus (.inr rfl) n p f h0) hn1 K hK b c hirr).2
  have hout : Nat.card (Outer T) = Nat.card (Outer (matrixProjectiveDerived Qc)) := by
    rw [hQc]
    exact Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (coordinateMinusWitnessEquiv K hn1 b c e)).toEquiv
  have hQ : ∃ v, Qc v ≠ 0 := by
    rw [hQc]
    exact exists_nonzero_value _ (coordinate_model_intrinsic_minus h0 K hK b c hirr e).1
  have ha := relIndex_inner_dvd Qc
  have hb := relIndex_isometryRange_dvd Qc hQ
  have hsqidx : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = Nat.gcd (Nat.card K - 1) 2 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
  rw [hsqidx] at hb
  have hc := (relIndex_linearRange_dvd Qc).trans
    ((Subgroup.card_subgroup_dvd_card (fieldProjection Qc).range).trans
      (card_ringAut_and_isCyclic hp K hK).1.dvd)
  obtain ⟨k, hk⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
      (minusIndexEquiv n hn1)
    (quadMinus n K b c) hab
  have hk' : Nat.card (Abelianization (matrixIsometries Qc)) = 2 ^ k := by
    rw [hQc]
    change Nat.card (Abelianization (matrixIsometries
      (reindexQuadraticForm (minusIndexEquiv n hn1) (quadMinus n K b c)))) = 2 ^ k
    exact hk
  have hkidx : (matrixProjectiveImage Qc).index = 1 := by
    rw [hE, Subgroup.index_top]
  rw [hout, card_outer_eq, hkidx, mul_one]
  set Inn := CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Qc)
    with hInn
  by_cases hp2 : p = 2
  ·
    subst hp2
    have hodd : Odd (((2 : ℕ) ^ f) ^ n + 1) := by
      have he : Even (((2 : ℕ) ^ f) ^ n) := by
        rw [← pow_mul]
        exact Even.pow_of_ne_zero even_two (Nat.mul_ne_zero (by omega) (by omega))
      exact he.add_odd odd_one
    have hgcd : Nat.gcd 4 (((2 : ℕ) ^ f) ^ n + 1) = 1 := by
      have h2c : Nat.Coprime 2 (((2 : ℕ) ^ f) ^ n + 1) := Nat.coprime_two_left.mpr hodd
      simpa using h2c.pow_left 2
    have hoddK : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow
        ((Nat.even_pow' (by omega)).mpr even_two) odd_one
    have hgcdK : Nat.gcd (Nat.card K - 1) 2 = 1 := by
      rw [hK]
      exact hoddK.coprime_two_right.gcd_eq_one
    have hbL : (isometryConjugationHom Qc).range.relIndex
        (linearConjugationHom Qc).range = 1 := by
      apply Nat.dvd_one.mp
      rwa [hgcdK] at hb
    have hAb2 : Nat.card (Abelianization (matrixIsometries Qc)) ≤ 2 := by
      rw [hQc]
      change Nat.card (Abelianization (matrixIsometries
        (reindexQuadraticForm (minusIndexEquiv n hn1) (quadMinus n K b c)))) ≤ 2
      rw [card_abelianization_matrixIsometries_reindex]
      exact hab.2.2 rfl
    have hAdv : Nat.card (Abelianization (matrixIsometries Qc)) ∣ 2 := by
      rw [hk']
      have hk1 : k ≤ 1 := by
        have hle : 2 ^ k ≤ 2 ^ 1 := by rw [← hk']; exact hAb2
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
      calc (2 : ℕ) ^ k ∣ 2 ^ 1 := Nat.pow_dvd_pow 2 hk1
        _ = 2 := by norm_num
    have hpa : Inn.relIndex
        (isometryConjugationHom Qc).range ∣ 2 := ha.trans hAdv
    have hprod : Inn.relIndex
          (isometryConjugationHom Qc).range *
        (isometryConjugationHom Qc).range.relIndex (linearConjugationHom Qc).range *
        (linearConjugationHom Qc).range.relIndex (matrixProjectiveImage Qc) ∣ 2 * f := by
      rw [hbL, mul_one]
      exact Nat.mul_dvd_mul hpa hc
    rw [hgcd, show 1 * f * 2 = 2 * f by ring]
    exact hprod
  ·
    have hodd : Odd (p ^ f) :=
      CFSG.ClassicalInvolution.odd_of_card_eq_prime_pow hp hp2 rfl
    have hsqiff : IsSquare ((-1 : K) ^ n) ↔ (p ^ f) ^ n % 4 = 1 :=
      CFSG.ClassicalInvolution.isSquare_neg_one_pow_iff hK hodd n
    have hpb : (isometryConjugationHom Qc).range.relIndex
        (linearConjugationHom Qc).range ∣ 2 := hb.trans (Nat.gcd_dvd_right _ _)
    have hAb4 : Nat.card (Abelianization (matrixIsometries Qc)) ≤ 4 := by
      rw [hQc]
      change Nat.card (Abelianization (matrixIsometries
        (reindexQuadraticForm (minusIndexEquiv n hn1) (quadMinus n K b c)))) ≤ 4
      rw [card_abelianization_matrixIsometries_reindex]
      exact hab.2.1 hp2
    have hAb4dvd : Nat.card (Abelianization (matrixIsometries Qc)) ∣ 4 := by
      rw [hk']
      have hk2 : k ≤ 2 := by
        have hle : 2 ^ k ≤ 2 ^ 2 := by rw [← hk']; simpa using hAb4
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
      calc (2 : ℕ) ^ k ∣ 2 ^ 2 := Nat.pow_dvd_pow 2 hk2
        _ = 4 := by norm_num
    by_cases hs : IsSquare ((-1 : K) ^ n)
    ·
      have hmod : (p ^ f) ^ n % 4 = 1 := hsqiff.mp hs
      have hg : Nat.gcd 4 ((p ^ f) ^ n + 1) = 2 := by
        apply CFSG.ClassicalInvolution.gcd_four_of_mod_two
        omega
      have h2 : (2 : K) ≠ 0 :=
        CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hK
      have hneg : (⟨-1, neg_one_mem_matrixIsometries Qc⟩ : matrixIsometries Qc) ∉
          commutator (matrixIsometries Qc) := by
        intro hmem
        have hD : (-1 : GL (Fin (2 * n)) K) ∈ matrixDerived Qc := by
          rw [matrixDerived_eq_map_commutator]
          exact ⟨_, hmem, rfl⟩
        have hval := statedDerivedReindexEquiv_symm_val (minusIndexEquiv n hn1)
          (quadMinus n K b c) (coe_quadMinus n K b c) ⟨-1, hD⟩
        have hm1 : (reindexMatrixEquiv (minusIndexEquiv n hn1)).symm
            (-1 : GL (Fin (2 * n)) K) = -1 := by
          rw [MulEquiv.symm_apply_eq]
          ext i j
          simp [reindexMatrixEquiv_val, Matrix.neg_apply, Matrix.one_apply]
        have hO := ((statedDerivedReindexEquiv (minusIndexEquiv n hn1) (quadMinus n K b c)
          (coe_quadMinus n K b c)).symm ⟨-1, hD⟩).property
        rw [hval, hm1] at hO
        exact neg_one_not_mem_statedOmega_quadMinus hn h2 hirr hs hO
      have hpa : Inn.relIndex
          (isometryConjugationHom Qc).range ∣ 2 := by
        have h2a := two_mul_relIndex_inner_le Qc hneg
        rw [← hInn] at h2a
        have hpos : 0 < Inn.relIndex
            (isometryConjugationHom Qc).range :=
          Nat.pos_of_dvd_of_pos ha Nat.card_pos
        have hle : Inn.relIndex
            (isometryConjugationHom Qc).range ≤ 2 := by omega
        rcases (by omega : Inn.relIndex
            (isometryConjugationHom Qc).range = 1 ∨
            Inn.relIndex
              (isometryConjugationHom Qc).range = 2) with h1 | h1
        · simp [h1]
        · simp [h1]
      have hprod : Inn.relIndex
            (isometryConjugationHom Qc).range *
          (isometryConjugationHom Qc).range.relIndex (linearConjugationHom Qc).range *
          (linearConjugationHom Qc).range.relIndex (matrixProjectiveImage Qc) ∣ 2 * 2 * f :=
        Nat.mul_dvd_mul (Nat.mul_dvd_mul hpa hpb) hc
      rw [hg, show 2 * f * 2 = 2 * 2 * f by ring]
      exact hprod
    ·
      have hmod : (p ^ f) ^ n % 4 = 3 := by
        rcases CFSG.ClassicalInvolution.odd_pow_mod_four hodd n with h1 | h3
        · exact absurd (hsqiff.mpr h1) hs
        · exact h3
      have hg : Nat.gcd 4 ((p ^ f) ^ n + 1) = 4 := by
        apply CFSG.ClassicalInvolution.gcd_four_of_mod_zero
        omega
      have hpa : Inn.relIndex
          (isometryConjugationHom Qc).range ∣ 4 := ha.trans hAb4dvd
      have hprod : Inn.relIndex
            (isometryConjugationHom Qc).range *
          (isometryConjugationHom Qc).range.relIndex (linearConjugationHom Qc).range *
          (linearConjugationHom Qc).range.relIndex (matrixProjectiveImage Qc) ∣ 4 * 2 * f :=
        Nat.mul_dvd_mul (Nat.mul_dvd_mul hpa hpb) hc
      rw [hg, show 4 * f * 2 = 4 * 2 * f by ring]
      exact hprod

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
