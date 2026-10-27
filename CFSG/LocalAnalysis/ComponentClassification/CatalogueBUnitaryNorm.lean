module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentField
public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.ComponentClassification.CatalogueBUnitaryNorm

noncomputable section

universe u

variable {K : Type u} [Field K] (sigma : K ≃+* K)

theorem involutive (hsigma : sigma ^ 2 = 1) :
    Function.Involutive sigma := by
  intro x
  have hx := DFunLike.congr_fun hsigma x
  change (sigma ^ 2) x = x
  exact hx

theorem exists_not_fixed (hne : sigma ≠ 1) : ∃ x : K, sigma x ≠ x := by
  by_contra! h
  apply hne
  ext x
  exact h x

theorem exists_trace_ne_zero (hne : sigma ≠ 1) :
    ∃ x : K, x + sigma x ≠ 0 := by
  by_contra! h
  obtain ⟨c, hc⟩ := exists_not_fixed sigma hne
  have h1 := h 1
  have h2 := h c
  rw [map_one] at h1
  apply hc
  linear_combination h2 - c * h1

theorem exists_trace (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (a : K) (ha : sigma a = a) : ∃ x : K, x + sigma x = a := by
  obtain ⟨c, hc⟩ := exists_trace_ne_zero sigma hne
  have hfixed : sigma (c + sigma c) = c + sigma c := by
    rw [map_add, involutive sigma hsigma, add_comm]
  refine ⟨(a / (c + sigma c)) * c, ?_⟩
  rw [map_mul, map_div₀, ha, hfixed]
  field_simp

theorem exists_norm [Finite K] (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (d : K) (hd : sigma d = d) (hd0 : d ≠ 0) :
    ∃ c : K, sigma c * c = d := by
  obtain ⟨b, hb⟩ :=
    CatalogueBLinearTwoDescent.exists_norm_unit K sigma hsigma hne (Units.mk0 d hd0) hd
  exact ⟨b, (mul_comm _ _).trans hb⟩

theorem isUnitaryInvolution [Finite K] (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution sigma where
  invol := involutive sigma hsigma
  exists_ne := exists_not_fixed sigma hne
  trace_surj := exists_trace sigma hsigma hne
  norm_surj := exists_norm sigma hsigma hne

theorem exists_norm_one_ratio (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (a : Kˣ) (ha : sigma (a : K) * (a : K) = 1) :
    ∃ b : Kˣ, (b : K) / sigma (b : K) = (a : K) := by
  have hex : ∃ x : K, x + (a : K) * sigma x ≠ 0 := by
    by_contra! hz
    have h1 := hz 1
    rw [map_one, mul_one] at h1
    obtain ⟨c, hc⟩ := exists_not_fixed sigma hne
    have h2 := hz c
    apply hc
    linear_combination sigma c * h1 - h2
  obtain ⟨x, hx⟩ := hex
  let b := x + (a : K) * sigma x
  have hb : (a : K) * sigma b = b := by
    dsimp [b]
    rw [map_add, map_mul, involutive sigma hsigma]
    linear_combination x * ha
  refine ⟨Units.mk0 b hx, ?_⟩
  change b / sigma b = (a : K)
  exact (div_eq_iff ((map_ne_zero sigma).mpr hx)).mpr hb.symm

end

end CFSG.ComponentClassification.CatalogueBUnitaryNorm
