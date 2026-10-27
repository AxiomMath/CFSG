module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8b
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8c
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup Module
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

theorem dvd_ordA {ℓ q : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hq : 1 ≤ q) (hdvd : ℓ ∣ q ^ 4 + 1) :
    ℓ ∣ CFSG.Open.ordA 1 (q ^ 4) := by
  have hQ : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have e1 : CFSG.Open.ordA 1 (q ^ 4) = q ^ 4 * ((q ^ 4) ^ 2 - 1) / Nat.gcd 2 (q ^ 4 - 1) := by
    simp [CFSG.Open.ordA]
  obtain ⟨k, hk⟩ : ∃ k, q ^ 4 = k + 1 := ⟨q ^ 4 - 1, by omega⟩
  have e2 : (q ^ 4) ^ 2 - 1 = (q ^ 4 + 1) * k := by
    rw [hk]
    have : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
    omega
  have hg : Nat.gcd 2 (q ^ 4 - 1) ∣ q ^ 4 * ((q ^ 4) ^ 2 - 1) := by
    refine (Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_left ?_ _)
    rw [e2, hk, Nat.add_sub_cancel]
    exact Dvd.intro_left _ rfl
  have h1 : ℓ ∣ q ^ 4 * ((q ^ 4) ^ 2 - 1) := by
    rw [e2]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hdvd _) _
  rw [e1]
  rw [← Nat.div_mul_cancel hg] at h1
  rcases (Nat.Prime.dvd_mul hℓ).mp h1 with h | h
  · exact h
  · exfalso
    have h2 := h.trans (Nat.gcd_dvd_left 2 (q ^ 4 - 1))
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h2)

attribute [local instance] GSThmB.Catalog7Std.Om8.finite_linearEquiv

variable {K : Type} [Field K] [Finite K] {b c : K}

theorem not_isSquare {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hQ0 : ∃ v, Q8 K b c v ≠ 0) (φ : MulAut (G0 K b c))
    (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (μ c₀ : Kˣ)
    (hsim : ∀ x, Q8 K b c (A x) = (μ : K) * Q8 K b c x) (hsq : ∀ x, A (A x) = (c₀ : K) • x)
    (hμc : (μ : K) = c₀) (hns : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K (Fin (2 * 4) → K)))
    (hφ : ∀ x, theta K b c hQ0 (φ x) =
      projectiveConjugation (Q8 K b c) A μ hsim (theta K b c hQ0 x))
    (J' : Subgroup (G0 K b c)) (hJφ : J' ≤ OutInv.fixSub φ)
    (hJ : IsComponent (J'.subgroupOf (OutInv.fixSub φ)))
    (hJm : Blueprint.LieModel (J' ⧸ center J') .PSL 2 p (2 * (2 * e))) :
    ¬ IsSquare (c₀ : K) := by
  rintro ⟨β, hβ⟩
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hβ
    exact Units.ne_zero _ hβ
  obtain ⟨M, -, hJM, -⟩ := exists_lift hQ0 φ A μ hsim hφ J' hJφ hJ
  have hMC := card_dvd_centralizer A μ hsim M
  have hstated := stated K b c hp he hK hirr
  obtain ⟨-, hnd, -⟩ := CatalogueBOrthogonalPointData.coordinate_model_witness_minus hstated K hK
    b c hirr (MulEquiv.refl _)
  obtain ⟨-, -, hA, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure p e hp hp2 he
      hK (by simp) (Q8 K b c) hnd A c₀ μ hsq (polar_similarity (Q8 K b c) A μ hsim) hns
  have hμd : (μ : K) / (c₀ : K) = 1 := by rw [hμc]; exact div_self (Units.ne_zero _)
  obtain ⟨hcompl, hW, hW', hpos, -⟩ :=
    hA (Units.mk0 β hβ0) (by rw [Units.val_mk0, hβ, sq])
  obtain ⟨-, hnd₁, hnd₂, ι, -⟩ := hpos hμd
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [Module.finrank_fin_fun] at hsum
  have h1 : 1 ≤ finrank K (positiveSquareKernel A (Units.mk0 β hβ0 : K)) := by
    by_contra h
    exact hW (Submodule.finrank_eq_zero.mp (by omega))
  have h1' : 1 ≤ finrank K (negativeSquareKernel A (Units.mk0 β hβ0 : K)) := by
    by_contra h
    exact hW' (Submodule.finrank_eq_zero.mp (by omega))
  have hq3 : 3 ≤ Nat.card K := by
    rw [hK]
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    exact le_trans h3 (Nat.le_self_pow (by omega) p)
  have hqodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨ℓ, hℓ, hℓ2, hℓdvd⟩ := exists_odd_prime_dvd_pow_four_add_one hqodd hq3
  have hchar : ringChar K ≠ 2 := by
    rw [ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp he hK]
    exact hp2
  have hJℓ : ℓ ∣ Nat.card J' := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center J'),
      GH74.card_of_lieModel_PSL (by norm_num) hJm]
    have h4 : p ^ (2 * (2 * e)) = (Nat.card K) ^ 4 := by rw [hK, ← pow_mul]; ring_nf
    rw [show 2 - 1 = 1 from rfl, h4]
    exact Dvd.dvd.mul_right (dvd_ordA hℓ hℓ2 (by omega) hℓdvd) _
  have hprod := (hJℓ.trans hJM).trans hMC
  rw [Nat.card_congr ι.toEquiv, Nat.card_prod] at hprod
  rcases (Nat.Prime.dvd_mul hℓ).mp hprod with h | h
  · exact not_dvd_card (Q := (Q8 K b c).comp (positiveSquareKernel A (Units.mk0 β hβ0 : K)).subtype)
      hℓ hℓ2 hℓdvd hchar hnd₁ h1 (by omega) h
  · exact not_dvd_card (Q := (Q8 K b c).comp (negativeSquareKernel A (Units.mk0 β hβ0 : K)).subtype)
      hℓ hℓ2 hℓdvd hchar hnd₂ h1' (by omega) h

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
