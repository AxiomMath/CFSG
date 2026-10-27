module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.AltSixCoreFour
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.AltSixCorePerm
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeKFactLift
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeKFactFixed
import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81EvenLift1
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core

theorem exists_lift_one_le_finrank_ker {F V : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Y G : Type*} [Group Y] [Finite Y]
    [Group G] (ψ : Y →* G) (hψ : Function.Surjective ψ) (ρ : Y →* (V ≃ₗ[F] V))
    (hρ : ρ.ker ≤ ψ.ker) (T : Subgroup G) (hT : Nat.Coprime (Nat.card ψ.ker) (Nat.card T))
    {u v w : G} (huT : u ∈ T) (hvT : v ∈ T) (hwT : w ∈ T) (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (huv : Commute u v) (hw : w ^ 3 = 1) (hwu : w * u * w⁻¹ = v) (hwv : w * v * w⁻¹ = u * v)
    (hu1 : u ≠ 1) :
    ∃ x : Y, ψ x = w ∧ x ^ 3 = 1 ∧
      1 ≤ Module.finrank F ↥(LinearMap.ker ((ρ x).toLinearMap - 1)) := by
  classical
  obtain ⟨σ, hσ⟩ :=
    CFSG.ComponentClassification.CatFC.DS81.exists_hom_section_of_coprime_card ψ hψ T hT
  have hu2 : (⟨u, huT⟩ : T) ^ 2 = 1 := Subtype.ext (by simpa using hu)
  have hv2 : (⟨v, hvT⟩ : T) ^ 2 = 1 := Subtype.ext (by simpa using hv)
  have hw3 : (⟨w, hwT⟩ : T) ^ 3 = 1 := Subtype.ext (by simpa using hw)
  have huvT : Commute (⟨u, huT⟩ : T) ⟨v, hvT⟩ := Subtype.ext (by simpa using huv.eq)
  have hwuT : (⟨w, hwT⟩ : T) * ⟨u, huT⟩ * (⟨w, hwT⟩ : T)⁻¹ = ⟨v, hvT⟩ :=
    Subtype.ext (by simpa using hwu)
  have hwvT : (⟨w, hwT⟩ : T) * ⟨v, hvT⟩ * (⟨w, hwT⟩ : T)⁻¹ =
      ⟨u, huT⟩ * ⟨v, hvT⟩ :=
    Subtype.ext (by simpa using hwv)
  have hσu2 : (σ ⟨u, huT⟩ : Y) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hσv2 : (σ ⟨v, hvT⟩ : Y) ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
  have hσw3 : (σ ⟨w, hwT⟩ : Y) ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
  refine ⟨σ ⟨w, hwT⟩, hσ ⟨w, hwT⟩, hσw3, ?_⟩
  refine one_le_finrank_ker_of_klein (K := F) (V := V)
    (u := ρ (σ ⟨u, huT⟩)) (v := ρ (σ ⟨v, hvT⟩)) (w := ρ (σ ⟨w, hwT⟩)) h2
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hσu2, map_one]
  · rw [← map_pow, hσv2, map_one]
  · exact (Commute.map huvT σ).map ρ
  · rw [← map_pow, hσw3, map_one]
  · simpa only [map_mul, map_inv] using congrArg ρ (congrArg σ hwuT)
  · simpa only [map_mul, map_inv] using congrArg ρ (congrArg σ hwvT)
  · intro h
    have hmem : σ ⟨u, huT⟩ ∈ ρ.ker := MonoidHom.mem_ker.mpr h
    have hmemψ : σ ⟨u, huT⟩ ∈ ψ.ker := hρ hmem
    have h1 : ψ (σ ⟨u, huT⟩) = 1 := MonoidHom.mem_ker.mp hmemψ
    rw [hσ ⟨u, huT⟩] at h1
    exact hu1 h1

private theorem coprime_six_alt {Y G : Type*} [Group Y] [Group G] {ψ : Y →* G}
    (hcop : Nat.Coprime (Nat.card ψ.ker) 6) :
    ¬ 3 ∣ Nat.card ψ.ker ∧ Nat.Coprime (Nat.card ψ.ker) 12 := by
  constructor
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (hcop.coprime_dvd_right (by norm_num : 3 ∣ 6)).symm
  · exact (hcop.pow_right 2).coprime_dvd_right (by norm_num : 12 ∣ 6 ^ 2)

private theorem finrank_ker_lt_of_map_eq {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Y G : Type*} [Group Y] [Group G] {ψ : Y →* G}
    {ρ : Y →* (V ≃ₗ[F] V)} (hρ : ρ.ker ≤ ψ.ker) {y : Y} {a : G}
    (hy : ψ y = a) (ha : a ≠ 1) :
    Module.finrank F ↥(LinearMap.ker ((ρ y).toLinearMap - 1)) < Module.finrank F V := by
  have hρy : ρ y ≠ 1 := by
    intro h
    have hmem : y ∈ ρ.ker := MonoidHom.mem_ker.mpr h
    exact ha (by rw [← hy, MonoidHom.mem_ker.mp (hρ hmem)])
  exact A9Lin.finrank_ker_sub_one_lt_finrank hρy

private theorem one_le_finrank_ker_of_isConj_lift {F V : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Y G : Type*} [Group Y] [Finite Y]
    [Group G] (ψ : Y →* G) (hψ : Function.Surjective ψ) (ρ : Y →* (V ≃ₗ[F] V))
    (hρ : ρ.ker ≤ ψ.ker) (T : Subgroup G) (hT : Nat.Coprime (Nat.card ψ.ker) (Nat.card T))
    {u v w : G} (huT : u ∈ T) (hvT : v ∈ T) (hwT : w ∈ T) (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (huv : Commute u v) (hw : w ^ 3 = 1) (hwu : w * u * w⁻¹ = v) (hwv : w * v * w⁻¹ = u * v)
    (hu1 : u ≠ 1) (h3ker : ¬ 3 ∣ Nat.card ψ.ker) {x : Y} (hx3 : x ^ 3 = 1)
    (hconj : IsConj w (ψ x)) :
    1 ≤ Module.finrank F ↥(LinearMap.ker ((ρ x).toLinearMap - 1)) := by
  obtain ⟨x', hx'ψ, hx'3, hx'1⟩ :=
    exists_lift_one_le_finrank_ker h2 ψ hψ ρ hρ T hT huT hvT hwT hu hv huv hw hwu hwv hu1
  have hconj' : IsConj x' x :=
    A9Lin.isConj_of_isConj_map_of_pow_three ψ hψ h3ker hx'3 hx3 (by rw [hx'ψ]; exact hconj)
  rw [← A9Lin.finrank_ker_eq_of_isConj ρ hconj']
  exact hx'1

private theorem alt_fixed_dimensions {F V : Type*} [Field F] [Finite F] (h3 : (3 : F) ≠ 0)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Y : Type*} [Group Y] [Finite Y]
    {ψ : Y →* alternatingGroup (Fin 6)} (hψ : Function.Surjective ψ)
    (h3ker : ¬ 3 ∣ Nat.card ψ.ker) (ρ : Y →* (V ≃ₗ[F] V)) {y z : Y}
    (hyψ : ψ y = aA6) (hzψ : ψ z = bA6) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1)
    (hyz : Commute y z) :
    Even (Module.finrank F V - Module.finrank F ↥(LinearMap.ker ((ρ y).toLinearMap - 1))) ∧
    Even (Module.finrank F V -
      Module.finrank F ↥(LinearMap.ker ((ρ (y * z)).toLinearMap - 1))) ∧
    Module.finrank F ↥(LinearMap.ker ((ρ z).toLinearMap - 1)) =
      Module.finrank F ↥(LinearMap.ker ((ρ y).toLinearMap - 1)) ∧
    Module.finrank F ↥(LinearMap.ker ((ρ (y * z ^ 2)).toLinearMap - 1)) =
      Module.finrank F ↥(LinearMap.ker ((ρ (y * z)).toLinearMap - 1)) := by
  have hyz3 : (y * z) ^ 3 = 1 := by rw [hyz.mul_pow, hy3, hz3, one_mul]
  have hyz2_3 : (y * z ^ 2) ^ 3 = 1 := by
    have h : (z ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hz3, one_pow]
    rw [(hyz.pow_right 2).mul_pow, hy3, h, one_mul]
  have hzy : IsConj z y :=
    A9Lin.isConj_of_isConj_map_of_pow_three ψ hψ h3ker hz3 hy3
      (by rw [hzψ, hyψ]; exact isConj_bA6_aA6)
  have hyz2yz : IsConj (y * z ^ 2) (y * z) :=
    A9Lin.isConj_of_isConj_map_of_pow_three ψ hψ h3ker hyz2_3 hyz3 (by
      rw [map_mul, map_pow, map_mul, hyψ, hzψ]
      exact isConj_aA6_mul_bA6_sq)
  have hyinv : IsConj y y⁻¹ :=
    A9Lin.isConj_of_isConj_map_of_pow_three ψ hψ h3ker hy3 (by rw [inv_pow, hy3, inv_one])
      (by rw [hyψ, map_inv, hyψ]; exact isConj_aA6_inv)
  have hyzinv : IsConj (y * z) (y * z)⁻¹ :=
    A9Lin.isConj_of_isConj_map_of_pow_three ψ hψ h3ker hyz3
      (by rw [inv_pow, hyz3, inv_one])
      (by simp only [map_mul, map_inv, hyψ, hzψ]; exact isConj_aA6_mul_bA6_inv)
  exact ⟨A9Lin.even_finrank_sub_of_isConj_inv h3 ρ hy3 hyinv,
    A9Lin.even_finrank_sub_of_isConj_inv h3 ρ hyz3 hyzinv,
    A9Lin.finrank_ker_eq_of_isConj ρ hzy,
    A9Lin.finrank_ker_eq_of_isConj ρ hyz2yz⟩

private theorem false_of_bounds {m d₁ d₂ c₀ : ℕ} (hm : m ≤ 4) (hd₁ : 1 ≤ d₁) (hd₁' : d₁ < m)
    (hd₂ : 1 ≤ d₂) (hd₂' : d₂ ≤ m) (hc₀ : c₀ ≤ m) (he₁ : Even (m - d₁))
    (he₂ : Even (m - d₂)) (hBW : m + 3 * c₀ = 2 * d₁ + 2 * d₂) : False := by
  obtain ⟨a, ha⟩ := he₁
  obtain ⟨b, hb⟩ := he₂
  omega

theorem false_of_finrank_le_four {F V : Type*} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : Module.finrank F V ≤ 4) {Y : Type*} [Group Y] [Finite Y]
    (ψ : Y →* alternatingGroup (Fin 6)) (hψ : Function.Surjective ψ)
    (hcop : Nat.Coprime (Nat.card ψ.ker) 6) (ρ : Y →* (V ≃ₗ[F] V)) (hρ : ρ.ker ≤ ψ.ker) :
    False := by
  classical
  obtain ⟨h3ker, hcop12⟩ := coprime_six_alt hcop
  obtain ⟨y, z, hyψ, hzψ, hy3, hz3, hyz⟩ :=
    A9Lin.exists_lift_commute_of_pow_three ψ hψ h3ker aA6_pow_three bA6_pow_three
      commute_aA6_bA6
  set m : ℕ := Module.finrank F V with hm
  set d₁ : ℕ := Module.finrank F ↥(LinearMap.ker ((ρ y).toLinearMap - 1)) with hd₁
  set d₂ : ℕ := Module.finrank F ↥(LinearMap.ker ((ρ (y * z)).toLinearMap - 1)) with hd₂
  set c₀ : ℕ := Module.finrank F ↥(LinearMap.ker ((ρ y).toLinearMap - 1) ⊓
    LinearMap.ker ((ρ z).toLinearMap - 1)) with hc₀
  obtain ⟨heven1, heven2, hdimz, hdimyz2⟩ :=
    alt_fixed_dimensions h3 hψ h3ker ρ hyψ hzψ hy3 hz3 hyz
  have heven1' : Even (m - d₁) := by simpa only [hm, hd₁] using heven1
  have heven2' : Even (m - d₂) := by simpa only [hm, hd₂] using heven2
  have hd₁_lt : d₁ < m := by
    rw [hd₁, hm]; exact finrank_ker_lt_of_map_eq hρ hyψ aA6_ne_one
  have hd₁_ge : 1 ≤ d₁ := by
    rw [hd₁]
    exact one_le_finrank_ker_of_isConj_lift h2 ψ hψ ρ hρ fourPtA6
      (by rw [card_fourPtA6]; exact hcop12) uA6_mem_fourPtA6 vPtA6_mem_fourPtA6
      wPtA6_mem_fourPtA6 uA6_sq vPtA6_sq commute_uA6_vPtA6 wPtA6_pow_three
      wPtA6_mul_uA6_mul_inv wPtA6_mul_vPtA6_mul_inv uA6_ne_one h3ker hy3
      (by rw [hyψ]; exact isConj_wPtA6_aA6)
  have hd₂_ge : 1 ≤ d₂ := by
    rw [hd₂]
    exact one_le_finrank_ker_of_isConj_lift h2 ψ hψ ρ hρ fourTrA6
      (by rw [card_fourTrA6]; exact hcop12) uA6_mem_fourTrA6 vTrA6_mem_fourTrA6
      wTrA6_mem_fourTrA6 uA6_sq vTrA6_sq commute_uA6_vTrA6 wTrA6_pow_three
      wTrA6_mul_uA6_mul_inv wTrA6_mul_vTrA6_mul_inv uA6_ne_one h3ker
      (by rw [hyz.mul_pow, hy3, hz3, one_mul]) (by rw [map_mul, hyψ, hzψ]; exact isConj_wTrA6_mul)
  have hd₂_le : d₂ ≤ m := by rw [hd₂, hm]; exact Submodule.finrank_le _
  have hc₀_le : c₀ ≤ m := by rw [hc₀, hm]; exact Submodule.finrank_le _
  have hBW' : m + 3 * c₀ = 2 * d₁ + 2 * d₂ := by
    have h := A9Lin.finrank_add_three_mul_finrank_inf_map h3 ρ hy3 hz3 hyz
    rw [← hc₀, hdimz, ← hd₁, hdimyz2, ← hd₂, ← hm] at h
    omega
  exact false_of_bounds (by rw [hm]; exact hV) hd₁_ge hd₁_lt hd₂_ge hd₂_le hc₀_le heven1'
    heven2' hBW'

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core
