module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeKFactPerm
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeKFactLift
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeKFactFixed

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin

open Module

private theorem eight_le_add_of_brauer_wielandt {m c₀ δ : ℕ} (h4 : m + 3 * c₀ = 4 * δ)
    (hc₀ : c₀ ≤ δ) (hδ : δ ≤ m) (heven : Even (m - δ)) (hpos : 0 < m - δ) :
    8 + c₀ ≤ m := by
  have h4' : 4 * (m - δ) = 3 * (m - c₀) := by omega
  obtain ⟨j, hj⟩ := heven
  have h8j : 8 * j = 3 * (m - c₀) := by omega
  have h3j : 3 ∣ j :=
    (Nat.prime_three.dvd_mul.mp ⟨m - c₀, h8j⟩).resolve_left (by norm_num)
  obtain ⟨i, hi⟩ := h3j
  have he : m - δ = 6 * i := by rw [hj, hi]; ring
  have hge : 6 ≤ m - δ := by
    have hi1 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with h | h
      · rw [h, mul_zero] at he
        omega
      · exact h
    omega
  omega

private theorem brauer_wielandt_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hK : (3 : K) ≠ 0) {X : Type*} [Group X] (ρ : X →* (V ≃ₗ[K] V))
    {y z : X} (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hyz : Commute y z)
    (hδz : Module.finrank K ↥(LinearMap.ker ((ρ z).toLinearMap - 1)) =
      Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1)))
    (hδyz : Module.finrank K ↥(LinearMap.ker ((ρ (y * z)).toLinearMap - 1)) =
      Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1)))
    (hδyz2 : Module.finrank K ↥(LinearMap.ker ((ρ (y * z ^ 2)).toLinearMap - 1)) =
      Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1))) :
    Module.finrank K V + 3 * Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1) ⊓
        LinearMap.ker ((ρ z).toLinearMap - 1)) =
      4 * Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1)) := by
  have hBW := finrank_add_three_mul_finrank_inf_map hK ρ hy3 hz3 hyz
  rw [hδz, hδyz, hδyz2] at hBW
  omega

theorem exists_commute_eight_add_finrank_le {K V : Type*} [Field K] [Finite K]
    (hK : (3 : K) ≠ 0) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {X : Type*} [Group X] [Finite X] (ρ : X →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ)
    (ψ : X →* alternatingGroup (Fin 9)) (hψ : Function.Surjective ψ)
    (h3 : ¬ 3 ∣ Nat.card ψ.ker) :
    ∃ y z : X, y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ Commute y z ∧
      8 + Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1) ⊓
        LinearMap.ker ((ρ z).toLinearMap - 1)) ≤ Module.finrank K V := by
  classical
  obtain ⟨y, z, hy, hz, hy3, hz3, hyz⟩ :=
    exists_lift_commute_of_pow_three ψ hψ h3 vA9_pow_three tA9_pow_three commute_vA9_tA9
  refine ⟨y, z, hy3, hz3, hyz, ?_⟩
  have hyz3 : (y * z) ^ 3 = 1 := by rw [hyz.mul_pow, hy3, hz3, one_mul]
  have hcomm_z2 : Commute y (z ^ 2) := hyz.pow_right 2
  have hz2_3 : (z ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hz3, one_pow]
  have hyz2_3 : (y * z ^ 2) ^ 3 = 1 := by rw [hcomm_z2.mul_pow, hy3, hz2_3, one_mul]
  have hψyz : ψ (y * z) = vA9 * tA9 := by rw [map_mul, hy, hz]
  have hψyz2 : ψ (y * z ^ 2) = vA9 * tA9 ^ 2 := by rw [map_mul, map_pow, hy, hz]
  have hψyinv : ψ y⁻¹ = vA9⁻¹ := by rw [map_inv, hy]
  have hδz : Module.finrank K ↥(LinearMap.ker ((ρ z).toLinearMap - 1)) =
      Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1)) :=
    finrank_ker_eq_of_isConj ρ
      (isConj_of_isConj_map_of_pow_three ψ hψ h3 hz3 hy3 (by rw [hz, hy]; exact isConj_tA9_vA9))
  have hδyz : Module.finrank K ↥(LinearMap.ker ((ρ (y * z)).toLinearMap - 1)) =
      Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1)) :=
    finrank_ker_eq_of_isConj ρ (isConj_of_isConj_map_of_pow_three ψ hψ h3 hyz3 hy3
      (by rw [hψyz, hy]; exact isConj_vA9_mul_tA9))
  have hδyz2 : Module.finrank K ↥(LinearMap.ker ((ρ (y * z ^ 2)).toLinearMap - 1)) =
      Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1)) :=
    finrank_ker_eq_of_isConj ρ (isConj_of_isConj_map_of_pow_three ψ hψ h3 hyz2_3 hy3
      (by rw [hψyz2, hy]; exact isConj_vA9_mul_tA9_sq))
  have hconj_inv : IsConj y y⁻¹ :=
    isConj_of_isConj_map_of_pow_three ψ hψ h3 hy3 (by rw [inv_pow, hy3, inv_one])
      (by rw [hψyinv, hy]; exact isConj_vA9_inv)
  have hyne : y ≠ 1 := by
    intro h
    rw [h, map_one] at hy
    exact vA9_ne_one hy.symm
  have hpos : 0 < Module.finrank K V -
      Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1)) := by
    have := finrank_ker_sub_one_lt_finrank (K := K) (V := V) (g := ρ y)
      fun h => hyne (hρ (by rw [h, map_one]))
    omega
  exact eight_le_add_of_brauer_wielandt (brauer_wielandt_finrank hK ρ hy3 hz3 hyz hδz hδyz hδyz2)
    (Submodule.finrank_mono inf_le_left) (Submodule.finrank_le _)
    (even_finrank_sub_of_isConj_inv hK ρ hy3 hconj_inv) hpos

theorem toLinearMap_generalLinearEquiv_toLin {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (A : GL ι K) :
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))
        (Matrix.GeneralLinearGroup.toLin A)).toLinearMap = Matrix.toLin' (A : Matrix ι ι K) := by
  ext v
  simp [Matrix.GeneralLinearGroup.coe_toLin,
    LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap, Matrix.toLin'_apply]

theorem exists_commute_eight_add_finrank_le_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] [Finite K] (hK : (3 : K) ≠ 0) (X : Subgroup (GL ι K))
    (ψ : X →* alternatingGroup (Fin 9)) (hψ : Function.Surjective ψ)
    (h3 : ¬ 3 ∣ Nat.card ψ.ker) :
    ∃ y ∈ X, ∃ z ∈ X, y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ Commute y z ∧
      8 + Module.finrank K ↥(LinearMap.ker (Matrix.toLin' (y : Matrix ι ι K) - 1) ⊓
        LinearMap.ker (Matrix.toLin' (z : Matrix ι ι K) - 1)) ≤ Fintype.card ι := by
  classical
  let ρ : X →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp X.subtype)
  have hρ : Function.Injective ρ := by
    intro a b hab
    have h2 := (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).injective hab
    exact Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective h2)
  obtain ⟨y, z, hy3, hz3, hyz, hle⟩ :=
    exists_commute_eight_add_finrank_le (K := K) (V := ι → K) hK ρ hρ ψ hψ h3
  refine ⟨(y : GL ι K), y.2, (z : GL ι K), z.2, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val hy3
  · simpa using congrArg Subtype.val hz3
  · simpa using hyz
  · have hkey : ∀ w : X, (ρ w).toLinearMap = Matrix.toLin' ((w : GL ι K) : Matrix ι ι K) :=
      fun w => toLinearMap_generalLinearEquiv_toLin (w : GL ι K)
    have h := hle
    rw [Module.finrank_fintype_fun_eq_card] at h
    rwa [← hkey y, ← hkey z]

theorem eight_le_card_of_surjective {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*}
    [Field K] [Finite K] (hK : (3 : K) ≠ 0) (X : Subgroup (GL ι K))
    (ψ : X →* alternatingGroup (Fin 9)) (hψ : Function.Surjective ψ)
    (h3 : ¬ 3 ∣ Nat.card ψ.ker) : 8 ≤ Fintype.card ι := by
  obtain ⟨y, -, z, -, -, -, -, hle⟩ := exists_commute_eight_add_finrank_le_card hK X ψ hψ h3
  have h0 : 0 ≤ Module.finrank K ↥(LinearMap.ker (Matrix.toLin' (y : Matrix ι ι K) - 1) ⊓
      LinearMap.ker (Matrix.toLin' (z : Matrix ι ι K) - 1)) := Nat.zero_le _
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin
