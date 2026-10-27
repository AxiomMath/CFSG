module

public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.LieType.Chevalley CFSG.RankThree.Chevalley.SteinbergBT

theorem exists_frobenius_of_cube {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    ∃ (d : ℕ) (T : K ≃+* K), 0 < d ∧ d * 3 = f ∧ (∀ c, T c = c ^ ℓ ^ d) ∧ T ^ 3 = 1 ∧
      (σ = T ∨ σ = T ^ 2) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  have hσp : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨hpf, -⟩ := card_fixSubfield hℓ hf hK σ
  rw [hσp] at hpf
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      hℓ hf hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  obtain ⟨d, hd⟩ := hpf
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * 3 = f := by rw [hd, mul_comm]
  have hσmem : σ ∈ Subgroup.zpowers fr := by rw [hgen]; exact Subgroup.mem_top σ
  obtain ⟨k, hk, hkσ⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hσmem)
  replace hkσ : fr ^ k = σ := hkσ
  rw [Finset.mem_range, hord] at hk
  have hdk : d ∣ k := by
    have h1 : f ∣ k * 3 := by
      rw [← hord]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul, hkσ, hσ3]
    rw [← hdp] at h1
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1
  obtain ⟨j, rfl⟩ := hdk
  have hjp : j < 3 := by
    by_contra hjp
    have : d * 3 ≤ d * j := Nat.mul_le_mul_left d (not_lt.1 hjp)
    omega
  have hj0 : 0 < j := by
    refine Nat.pos_of_ne_zero fun hj => ?_
    rw [hj, mul_zero, pow_zero] at hkσ
    exact hσ1 hkσ.symm
  have hTj : (fr ^ d) ^ j = σ := by rw [← pow_mul, hkσ]
  have hTord : orderOf (fr ^ d) = 3 := by
    rw [orderOf_pow_of_dvd (by omega) (by rw [hord, ← hdp]; exact Dvd.intro 3 rfl), hord,
      ← hdp, Nat.mul_div_cancel_left 3 hd0]
  refine ⟨d, fr ^ d, hd0, hdp, fun c => ringAut_pow_apply_of_frobenius hfr d c,
    by rw [← hTord]; exact pow_orderOf_eq_one _, ?_⟩
  interval_cases j
  · exact Or.inl (by simpa using hTj.symm)
  · exact Or.inr hTj.symm

end CFSG.HardMathSupport.Lang.E6Descent
