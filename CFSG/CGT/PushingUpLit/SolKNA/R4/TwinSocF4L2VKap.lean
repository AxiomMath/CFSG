module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VMon
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VAlg

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.GorensteinWalter Matrix.ProjGenLinGroup CFSG.ClassicalInvolution.Q3.TL4.MF163

variable {K : Type} [Field K]

theorem conj_tor_inr (σ : K ≃+* K) (c : Kˣ) :
    (SemidirectProduct.inr σ : PGammaL2 K) * tor c * (SemidirectProduct.inr σ)⁻¹ =
      tor (umap σ c) := by
  rw [inr_mul_tor, mul_inv_cancel_right]

theorem conj_tor_wref (c : Kˣ) : (wref : PGammaL2 K) * tor c * wref⁻¹ = tor c⁻¹ := by
  rw [wref_mul_tor, mul_inv_cancel_right]

theorem conj_tor_tor (γ c : Kˣ) : (tor γ : PGammaL2 K) * tor c * (tor γ)⁻¹ = tor c := by
  rw [← map_mul, ← map_inv, ← map_mul, mul_comm γ c, mul_inv_cancel_right]

theorem tor_conj_mem (h2 : (2 : K) ≠ 0) {g : PGammaL2 K} (hg : g * tor (-1) = tor (-1) * g)
    (c : Kˣ) : ∃ c' : Kˣ, g * tor c * g⁻¹ = tor c' := by
  obtain ⟨γ, ε, σ, hε, rfl⟩ := exists_decomp h2 hg
  obtain rfl | rfl : ε = 0 ∨ ε = 1 := by omega
  · refine ⟨umap σ c, ?_⟩
    rw [pow_zero, mul_one]
    calc tor γ * SemidirectProduct.inr σ * tor c * (tor γ * SemidirectProduct.inr σ)⁻¹
        = tor γ * (SemidirectProduct.inr σ * tor c * (SemidirectProduct.inr σ)⁻¹) * (tor γ)⁻¹ := by
          group
      _ = _ := by rw [conj_tor_inr, conj_tor_tor]
  · refine ⟨(umap σ c)⁻¹, ?_⟩
    rw [pow_one]
    calc tor γ * wref * SemidirectProduct.inr σ * tor c *
          (tor γ * wref * SemidirectProduct.inr σ)⁻¹
        = tor γ * (wref * (SemidirectProduct.inr σ * tor c * (SemidirectProduct.inr σ)⁻¹) *
            wref⁻¹) * (tor γ)⁻¹ := by group
      _ = _ := by rw [conj_tor_inr, conj_tor_wref, conj_tor_tor]

theorem exists_pow_conj [Finite K] (h2 : (2 : K) ≠ 0) {g : PGammaL2 K}
    (hg : g * tor (-1) = tor (-1) * g) :
    ∃ m : ℕ, Odd m ∧ ∀ c : Kˣ, g * tor c * g⁻¹ = tor (c ^ m) := by
  classical
  choose f hf using tor_conj_mem h2 hg
  have hmul : ∀ c d, f (c * d) = f c * f d := by
    intro c d
    apply tor_injective
    rw [← hf, map_mul, map_mul, ← hf, ← hf]
    group
  obtain ⟨m, hm⟩ := exists_pow_eq_of_hom (MonoidHom.mk' f hmul)
  refine ⟨m, ?_, fun c => ?_⟩
  · have h1 : f (-1) = -1 := by
      apply tor_injective
      rw [← hf, hg]
      group
    have h3 : (-1 : Kˣ) ^ m = -1 := by
      have := hm (-1)
      simpa [h1] using this.symm
    by_contra hnodd
    rw [Nat.not_odd_iff_even] at hnodd
    rw [hnodd.neg_one_pow] at h3
    have h4 : ((1 : Kˣ) : K) = ((-1 : Kˣ) : K) := congrArg Units.val h3
    simp only [Units.val_one, Units.val_neg] at h4
    exact h2 (by linear_combination h4)
  · rw [hf, ← hm c]
    rfl


theorem tor_neg_one_sq : (tor (-1 : Kˣ) : PGammaL2 K) * tor (-1) = 1 := by
  rw [← map_mul]
  have : (-1 : Kˣ) * (-1) = 1 := by simp
  rw [this, map_one]

theorem tor_comm (a b : Kˣ) : (tor a : PGammaL2 K) * tor b = tor b * tor a := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem pow_tor_mul {μ : PGammaL2 K} {m : ℕ} (hm : ∀ c : Kˣ, μ * tor c * μ⁻¹ = tor (c ^ m))
    (γ : Kˣ) (j : ℕ) :
    (tor γ * μ) ^ j = tor (γ ^ (∑ i ∈ Finset.range j, m ^ i)) * μ ^ j := by
  have hconj : ∀ (i : ℕ) (c : Kˣ), μ ^ i * tor c * (μ ^ i)⁻¹ = tor (c ^ (m ^ i)) := by
    intro i
    induction i with
    | zero => intro c; simp
    | succ i ih =>
      intro c
      calc μ ^ (i + 1) * tor c * (μ ^ (i + 1))⁻¹
          = μ * (μ ^ i * tor c * (μ ^ i)⁻¹) * μ⁻¹ := by rw [pow_succ']; group
        _ = tor (c ^ (m ^ (i + 1))) := by rw [ih, hm, ← pow_mul, pow_succ, mul_comm (m ^ i) m]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih, Finset.sum_range_succ]
    have h1 : μ ^ j * tor γ = tor (γ ^ (m ^ j)) * μ ^ j := by
      have := hconj j γ
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    calc tor (γ ^ ∑ i ∈ Finset.range j, m ^ i) * μ ^ j * (tor γ * μ)
        = tor (γ ^ ∑ i ∈ Finset.range j, m ^ i) * (μ ^ j * tor γ) * μ := by group
      _ = tor (γ ^ ∑ i ∈ Finset.range j, m ^ i) * (tor (γ ^ (m ^ j)) * μ ^ j) * μ := by rw [h1]
      _ = tor ((γ ^ ∑ i ∈ Finset.range j, m ^ i) * γ ^ (m ^ j)) * (μ ^ j * μ) := by
        rw [map_mul]; group
      _ = _ := by rw [← pow_add, pow_succ]

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
