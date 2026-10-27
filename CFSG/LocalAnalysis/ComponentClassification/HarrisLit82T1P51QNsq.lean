module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticField

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix Polynomial CatalogueBProjectiveQuadratic

variable {K : Type} [Field K]

theorem quadExt_eq_add_mul_root (lam : K) (c : extension lam) :
    ∃ x y : K, c = algebraMap K (extension lam) x +
      algebraMap K (extension lam) y * AdjoinRoot.root (quadraticPolynomial lam) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective c
  have hf := quadraticPolynomial_monic lam
  have hdeg : (p %ₘ quadraticPolynomial lam).degree ≤ 1 := by
    have h1 := degree_modByMonic_lt p hf
    rw [degree_eq_natDegree hf.ne_zero, quadraticPolynomial_natDegree] at h1
    exact Order.le_of_lt_succ h1
  refine ⟨(p %ₘ quadraticPolynomial lam).coeff 0, (p %ₘ quadraticPolynomial lam).coeff 1, ?_⟩
  rw [← AdjoinRoot.mk_leftInverse hf (AdjoinRoot.mk _ p), AdjoinRoot.modByMonicHom_mk,
    eq_X_add_C_of_degree_le_one hdeg]
  simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, coeff_add, coeff_C_mul,
    coeff_X_one, coeff_X_zero, coeff_C, mul_one, mul_zero, add_zero, zero_add,
    one_ne_zero, ite_false]
  rw [add_comm]
  rfl

theorem quadExt_sq_mem (lam : K) [Fact (¬ IsSquare lam)] (htwo : (2 : K) ≠ 0)
    {c : extension lam} {ρ : K} (hc : c * c = algebraMap K (extension lam) ρ) :
    (∃ x : K, c = algebraMap K (extension lam) x) ∨
      ∃ y : K, c = algebraMap K (extension lam) y * AdjoinRoot.root (quadraticPolynomial lam) := by
  obtain ⟨x, y, rfl⟩ := quadExt_eq_add_mul_root lam c
  by_cases hx : x = 0
  · right
    exact ⟨y, by rw [hx, map_zero, zero_add]⟩
  by_cases hy : y = 0
  · left
    exact ⟨x, by rw [hy, map_zero, zero_mul, add_zero]⟩
  exfalso
  set ι := algebraMap K (extension lam)
  set θ := AdjoinRoot.root (quadraticPolynomial lam)
  have hθ : θ * θ = ι lam := by rw [← pow_two]; exact extension_root_square lam
  have h1 : (2 * ι x * ι y) * θ = ι ρ - ι x * ι x - ι lam * (ι y * ι y) := by
    linear_combination hc - (ι y * ι y) * hθ
  have hxy : (2 * ι x * ι y : extension lam) ≠ 0 := by
    have h2 : (2 * x * y : K) ≠ 0 := mul_ne_zero (mul_ne_zero htwo hx) hy
    have h3 := (map_ne_zero ι).mpr h2
    simpa only [map_mul, map_ofNat] using h3
  have hθk : θ = ι ((ρ - x * x - lam * (y * y)) / (2 * x * y)) := by
    simp only [map_div₀, map_sub, map_mul, map_ofNat]
    rw [← h1, mul_div_cancel_left₀ θ hxy]
  apply (Fact.out : ¬ IsSquare lam)
  refine ⟨(ρ - x * x - lam * (y * y)) / (2 * x * y), (algebraMap K (extension lam)).injective ?_⟩
  rw [← hθ, hθk, map_mul]

theorem card_quadExt [Finite K] (lam : K) [Fact (¬ IsSquare lam)] :
    Nat.card (extension lam) = Nat.card K ^ 2 := by
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Finite (extension lam) := Module.finite_of_finite K
  let _ : Fintype (extension lam) := Fintype.ofFinite _
  have h := Module.card_eq_pow_finrank (K := K) (V := extension lam)
  rw [extension_finrank lam, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  exact h

theorem exists_mul_self_eq_neg_one [Finite K] (lam : K) [Fact (¬ IsSquare lam)]
    (hodd : Odd (Nat.card K)) : ∃ ε : extension lam, ε * ε = -1 := by
  let _ : Finite (extension lam) := Module.finite_of_finite K
  let _ : Fintype (extension lam) := Fintype.ofFinite _
  have h4 : Fintype.card (extension lam) % 4 ≠ 3 := by
    rw [← Nat.card_eq_fintype_card, card_quadExt lam]
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    ring_nf
    omega
  obtain ⟨ε, hε⟩ := FiniteField.isSquare_neg_one_iff.mpr h4
  exact ⟨ε, hε.symm⟩

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
