module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAnisoAut

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' : Fin d} {b c : K}

theorem IsAnisoCoord.apply_mem_planeSub_of_fix (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate) {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgU : ∀ u ∈ perpSub K a a', g u = u)
    {w : Fin d → K} (hw : w ∈ planeSub K a a') : g w ∈ planeSub K a a' := by
  have hperp : ∀ y ∈ perpSub K a a', polar Q (g w) y = 0 := by
    intro y hy
    rw [← hgU y hy, polar_map_of_mem hgO, eq_planePart_of_mem h.ne hw]
    exact h.polar_plane_perp _ _ hy
  have h0 : perpPart a a' (g w) = 0 := by
    refine h.polarNondegOn_perpSub hQ _ (perpPart_mem h.ne _) fun y hy => ?_
    rw [h.polar_perpPart_left _ hy]
    exact hperp y hy
  rw [eq_add_perpPart a a' (g w), h0, add_zero]
  exact planePart_mem _

theorem IsAnisoCoord.mem_anisoRotSub_or_mul_self_eq_one [CharP K 2] (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate) {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgU : ∀ u ∈ perpSub K a a', g u = u) :
    g ∈ anisoRotSub h.ne b c ∨ g * g = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb : b ≠ 0 := by
    intro hb0
    have hz : (Pi.single a 1 : Fin d → K) = 0 :=
      eq_zero_of_polar_eq_zero hQ fun y => by rw [h.polar_left, hb0, zero_mul]
    have := congrFun hz a
    simp at this
  obtain ⟨p, s, hga⟩ : ∃ p s : K, g (Pi.single a 1) = p • Pi.single a 1 + s • Pi.single a' 1 :=
    ⟨_, _, eq_planePart_of_mem h.ne (h.apply_mem_planeSub_of_fix hQ hgO hgU
      single_left_mem_planeSub)⟩
  obtain ⟨r, t, hgb⟩ : ∃ r t : K, g (Pi.single a' 1) = r • Pi.single a 1 + t • Pi.single a' 1 :=
    ⟨_, _, eq_planePart_of_mem h.ne (h.apply_mem_planeSub_of_fix hQ hgO hgU
      single_right_mem_planeSub)⟩
  have hQplane : ∀ x y : K, Q (x • Pi.single a 1 + y • Pi.single a' 1) =
      x ^ 2 + b * x * y + c * y ^ 2 := by
    intro x y
    have := h.map_add_smul x y (p := 0) rfl rfl
    rwa [add_zero, QuadraticMap.map_zero, add_zero] at this
  have hE1 : p ^ 2 + b * p * s + c * s ^ 2 = 1 := by
    have h1 := map_of_mem hgO (Pi.single a 1)
    rw [hga, hQplane, h.map_left] at h1
    exact h1
  have hE3 : r ^ 2 + b * r * t + c * t ^ 2 = c := by
    have h1 := map_of_mem hgO (Pi.single a' 1)
    rw [hgb, hQplane, h.map_right] at h1
    exact h1
  have hE2 : p * t + s * r = 1 := by
    have h1 := polar_map_of_mem hgO (Pi.single a 1) (Pi.single a' 1)
    rw [hga, h.polar_plane_left, hgb, h.polar_left, Pi.single_eq_same] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne h.ne, Pi.single_eq_of_ne h.ne.symm, mul_one, mul_zero, add_zero,
      zero_add] at h1
    have : b * (p * t + s * r - 1) = 0 := by linear_combination h1
    linear_combination (mul_eq_zero.mp this).resolve_left hb
  obtain ⟨κ, hκ⟩ : ∃ κ : K, κ = (r - c * s) * p + b * (r - c * s) * s + c * (t - p - b * s) * s :=
    ⟨_, rfl⟩
  have hr : r = c * s + κ * p := by
    rw [hκ]
    linear_combination (-(r - c * s)) * hE1 + (c * s) * hE2 - (c * s) * hE1 -
      (c * s * p * (t - p - b * s)) * h2
  have ht : t = p + b * s + κ * s := by
    rw [hκ]
    linear_combination (-(t - p - b * s)) * hE1 + (p + b * s) * hE2 - (p + b * s) * hE1 -
      ((r - c * s) * s * (p + b * s)) * h2
  rw [hr, ht] at hE3
  have hκb : κ * (κ + b) = 0 := by
    linear_combination hE3 - (κ ^ 2 + b * κ + c) * hE1 -
      (b ^ 2 * c * s ^ 2 + 2 * c * κ * p * s + b * c * p * s + b * c * κ * s ^ 2) * h2
  have hdec : ∀ v : Fin d → K,
      v = v a • Pi.single a 1 + v a' • Pi.single a' 1 + perpPart a a' v :=
    fun v => eq_add_perpPart a a' v
  rcases mul_eq_zero.mp hκb with h0 | h0
  ·
    left
    refine ⟨p, s, hE1, fun v => ?_⟩
    rw [h0, zero_mul, add_zero] at hr ht
    conv_lhs => rw [hdec v]
    conv_rhs => rw [hdec v]
    rw [map_add, map_add, map_smul, map_smul, hga, hgb, hgU _ (perpPart_mem h.ne v), map_add,
      map_add, map_smul, map_smul, anisoRotLin_single_left h.ne, anisoRotLin_single_right h.ne,
      anisoRotLin_apply_of_mem_perpSub p s (perpPart_mem h.ne v), hr, ht]
  ·
    right
    have hκ' : κ = b := by linear_combination h0 - b * h2
    rw [hκ'] at hr ht
    have ht' : t = p := by linear_combination ht + (b * s) * h2
    have hgga : g (g (Pi.single a 1)) = Pi.single a 1 := by
      rw [hga, map_add, map_smul, map_smul, hga, hgb, hr]
      have e : p • (p • (Pi.single a 1 : Fin d → K) + s • Pi.single a' 1) +
          s • ((c * s + b * p) • Pi.single a 1 + t • Pi.single a' 1) =
          (p * p + s * (c * s + b * p)) • Pi.single a 1 + (p * s + s * t) • Pi.single a' 1 := by
        module
      rw [e, show p * p + s * (c * s + b * p) = 1 by linear_combination hE1,
        show p * s + s * t = 0 by rw [ht']; linear_combination (p * s) * h2, one_smul,
        zero_smul, add_zero]
    have hggb : g (g (Pi.single a' 1)) = Pi.single a' 1 := by
      rw [hgb, map_add, map_smul, map_smul, hga, hgb, hr]
      have e : (c * s + b * p) • (p • (Pi.single a 1 : Fin d → K) + s • Pi.single a' 1) +
          t • ((c * s + b * p) • Pi.single a 1 + t • Pi.single a' 1) =
          ((c * s + b * p) * p + t * (c * s + b * p)) • Pi.single a 1 +
            ((c * s + b * p) * s + t * t) • Pi.single a' 1 := by
        module
      rw [e, show (c * s + b * p) * p + t * (c * s + b * p) = 0 by
          rw [ht']; linear_combination ((c * s + b * p) * p) * h2,
        show (c * s + b * p) * s + t * t = 1 by rw [ht']; linear_combination hE1,
        zero_smul, zero_add, one_smul]
    refine LinearEquiv.ext fun v => ?_
    change g (g v) = v
    conv_lhs => rw [hdec v]
    conv_rhs => rw [hdec v]
    have hp := hgU _ (perpPart_mem h.ne v)
    simp only [map_add, map_smul, hgga, hggb, hp]

theorem IsAnisoCoord.mem_anisoRotSub_of_odd [CharP K 2] (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate) {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgU : ∀ u ∈ perpSub K a a', g u = u)
    (hodd : Odd (orderOf g)) : g ∈ anisoRotSub h.ne b c := by
  rcases h.mem_anisoRotSub_or_mul_self_eq_one hQ hgO hgU with hg | hg
  · exact hg
  · have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · rw [orderOf_eq_one_iff.mp h1]
      exact one_mem _
    · rw [h1] at hodd
      exact absurd hodd (by decide)

end CFSG.SeitzReduction.OmegaPilot
