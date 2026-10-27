module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagA

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def omegaLagSwap (Q : QuadraticForm K V) (s : V ≃ₗ[K] V) (a b : V) :
    V ≃ₗ[K] V :=
  eichler Q (omegaInvNil s (a + b)) (a + b)

section Swap

variable [CharP K 2] {s : V ≃ₗ[K] V} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
  (hss : s * s = 1) {a b : V} (ha : Q (omegaInvNil s a) = 1) (hb : Q (omegaInvNil s b) = 1)

include hs hss ha hb in
theorem omegaLagSwap_center :
    Q (omegaInvNil s (a + b)) = 0 ∧ polar Q (omegaInvNil s (a + b)) (a + b) = 0 := by
  have hQ0 : Q (omegaInvNil s (a + b)) = 0 := by
    rw [map_omegaInvNil_add hs hss, ha, hb]
    exact CharTwo.add_self_eq_zero 1
  exact ⟨hQ0, by rw [polar_omegaInvNil_self hs, hQ0]⟩

include hs hss ha hb in
theorem omegaLagSwap_apply (y : V) :
    omegaLagSwap Q s a b (omegaInvNil s y) = omegaInvNil s y +
      (polar Q (omegaInvNil s y) a + polar Q (omegaInvNil s y) b) • omegaInvNil s (a + b) := by
  obtain ⟨hQ0, hp0⟩ := omegaLagSwap_center hs hss ha hb
  have hyu : polar Q (omegaInvNil s y) (omegaInvNil s (a + b)) = 0 :=
    polar_of_mem_omegaInvSpace hs hss (omegaInvNil_mem_omegaInvSpace s y)
      (omegaInvNil_mem_omegaInvSpace s _)
  rw [omegaLagSwap, eichler_apply hQ0 hp0, hyu, zero_smul, add_zero, mul_zero, add_zero,
    polar_add_right, omegaInv_sub_eq_add K]

include hs hss ha hb in
theorem omegaLagSwap_props :
    omegaLagSwap Q s a b ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      omegaLagSwap Q s a b * s = s * omegaLagSwap Q s a b ∧
      omegaLagSwap Q s a b * omegaLagSwap Q s a b = 1 := by
  obtain ⟨hQ0, hp0⟩ := omegaLagSwap_center hs hss ha hb
  refine ⟨eichler_mem_orthogonalGroup Q _ _, ?_, ?_⟩
  · have e := eichler_conj hs (omegaInvNil s (a + b)) (a + b)
    have hsu : s (omegaInvNil s (a + b)) = omegaInvNil s (a + b) := apply_omegaInvNil hss _
    have hsw : s (a + b) = a + b + (1 : K) • omegaInvNil s (a + b) := by
      rw [one_smul, omegaInvNil_apply]
      abel
    rw [hsu, hsw, eichler_add_smul_self hQ0] at e
    rw [omegaLagSwap]
    calc eichler Q (omegaInvNil s (a + b)) (a + b) * s =
        (s * eichler Q (omegaInvNil s (a + b)) (a + b) * s⁻¹) * s := by rw [e]
      _ = s * eichler Q (omegaInvNil s (a + b)) (a + b) := by group
  · rw [omegaLagSwap, eichler_mul hp0 hp0, omegaInv_add_self K, eichler_zero_right]

end Swap

theorem reflect_mul_comm_of_mem_omegaInvSpace [CharP K 2] {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {w : V}
    (hw : w ∈ omegaInvSpace s) : reflect Q w * s = s * reflect Q w := by
  have e := reflect_conj hs w
  rw [apply_of_mem_omegaInvSpace hss hw] at e
  calc reflect Q w * s = (s * reflect Q w * s⁻¹) * s := by rw [e]
    _ = s * reflect Q w := by group

theorem reflect_mul_reflect_mem_omegaO2Cent [Finite K] [CharP K 2] [FiniteDimensional K V]
    {s : V ≃ₗ[K] V} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    {x₁ x₂ x₃ : V} (h1 : Q (omegaInvNil s x₁) = 1) (h2 : Q (omegaInvNil s x₂) = 1)
    (h3 : Q (omegaInvNil s x₃) = 1) (h12 : polar Q (omegaInvNil s x₁) x₂ = 0)
    (h13 : polar Q (omegaInvNil s x₁) x₃ = 0) (h23 : polar Q (omegaInvNil s x₂) x₃ = 0) :
    reflect Q (omegaInvNil s x₁) * reflect Q (omegaInvNil s x₂) ∈ omegaO2Cent Q s := by
  have hsym := polar_omegaInvNil_comm hs hss
  have hself : ∀ z, polar Q (omegaInvNil s z) z = Q (omegaInvNil s z) := polar_omegaInvNil_self hs
  have h21 : polar Q (omegaInvNil s x₂) x₁ = 0 := by rw [hsym, h12]
  have h31 : polar Q (omegaInvNil s x₃) x₁ = 0 := by rw [hsym, h13]
  have h32 : polar Q (omegaInvNil s x₃) x₂ = 0 := by rw [hsym, h23]
  obtain ⟨hσ₁₂O, hσ₁₂s, hσ₁₂σ⟩ := omegaLagSwap_props hs hss h1 h2
  obtain ⟨hσ₁₃O, hσ₁₃s, hσ₁₃σ⟩ := omegaLagSwap_props hs hss h1 h3
  have a12 := omegaLagSwap_apply hs hss h1 h2
  have a13 := omegaLagSwap_apply hs hss h1 h3
  have e121 : omegaLagSwap Q s x₁ x₂ (omegaInvNil s x₁) = omegaInvNil s x₂ := by
    rw [a12 x₁, hself x₁, h1, h12, add_zero, one_smul, map_add, ← add_assoc,
      omegaInv_add_self K, zero_add]
  have e122 : omegaLagSwap Q s x₁ x₂ (omegaInvNil s x₂) = omegaInvNil s x₁ := by
    rw [a12 x₂, h21, hself x₂, h2, zero_add, one_smul, map_add, add_comm (omegaInvNil s x₁),
      ← add_assoc, omegaInv_add_self K, zero_add]
  have e123 : omegaLagSwap Q s x₁ x₂ (omegaInvNil s x₃) = omegaInvNil s x₃ := by
    rw [a12 x₃, h31, h32, add_zero, zero_smul, add_zero]
  have e131 : omegaLagSwap Q s x₁ x₃ (omegaInvNil s x₁) = omegaInvNil s x₃ := by
    rw [a13 x₁, hself x₁, h1, h13, add_zero, one_smul, map_add, ← add_assoc,
      omegaInv_add_self K, zero_add]
  have e132 : omegaLagSwap Q s x₁ x₃ (omegaInvNil s x₂) = omegaInvNil s x₂ := by
    rw [a13 x₂, h21, h23, add_zero, zero_smul, add_zero]
  have e133 : omegaLagSwap Q s x₁ x₃ (omegaInvNil s x₃) = omegaInvNil s x₁ := by
    rw [a13 x₃, h31, hself x₃, h3, zero_add, one_smul, map_add, add_comm (omegaInvNil s x₁),
      ← add_assoc, omegaInv_add_self K, zero_add]
  set h₀ := omegaLagSwap Q s x₁ x₃ * omegaLagSwap Q s x₁ x₂ with hh₀
  have f1 : h₀ (omegaInvNil s x₁) = omegaInvNil s x₂ := by
    rw [hh₀, LinearEquiv.mul_apply, e121, e132]
  have f2 : h₀ (omegaInvNil s x₂) = omegaInvNil s x₃ := by
    rw [hh₀, LinearEquiv.mul_apply, e122, e131]
  have f3 : h₀ (omegaInvNil s x₃) = omegaInvNil s x₁ := by
    rw [hh₀, LinearEquiv.mul_apply, e123, e133]
  have hcube : ∀ v, (h₀ ^ 3) v = h₀ (h₀ (h₀ v)) := fun v => by
    rw [pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have g1 : (h₀ ^ 3) (omegaInvNil s x₁) = omegaInvNil s x₁ := by rw [hcube, f1, f2, f3]
  have g3 : (h₀ ^ 3) (omegaInvNil s x₃) = omegaInvNil s x₃ := by rw [hcube, f3, f1, f2]
  have h₀s : Commute h₀ s := Commute.mul_left hσ₁₃s hσ₁₂s
  have h₀sq : h₀ ^ 2 ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    have e : h₀ ^ 2 = ⁅omegaLagSwap Q s x₁ x₃, omegaLagSwap Q s x₁ x₂⁆ := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hσ₁₃σ,
        inv_eq_of_mul_eq_one_right hσ₁₂σ, _root_.sq, hh₀]
      simp only [mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator hσ₁₃O hσ₁₂O
  have : Finite (V ≃ₗ[K] V) := omegaPlane_finite_linearEquiv
  have hm0 : orderOf h₀ ≠ 0 := (isOfFinOrder_of_finite h₀).orderOf_pos.ne'
  obtain ⟨k, m, hm, hmk⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  set h := h₀ ^ (2 ^ (2 * k + 2)) with hh
  have hhm : h ^ m = 1 := by
    rw [hh, ← pow_mul, show 2 ^ (2 * k + 2) * m = orderOf h₀ * 2 ^ (k + 2) by rw [hmk]; ring,
      pow_mul, pow_orderOf_eq_one, one_pow]
  have hho : Odd (orderOf h) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hhm)
  have hhΩ : h ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [hh, show 2 ^ (2 * k + 2) = 2 * 2 ^ (2 * k + 1) by ring, pow_mul]
    exact pow_mem h₀sq _
  have hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q := omega_le_orthogonalGroup hhΩ
  have hhs : h ∈ Subgroup.centralizer ({s} : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h₀s.pow_left _).eq
  have he3 : 2 ^ (2 * k + 2) % 3 = 1 := by
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul, Nat.pow_mod]
    norm_num
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ (2 * k + 2) = 3 * q + 1 := ⟨2 ^ (2 * k + 2) / 3, by omega⟩
  have hpow : ∀ v, h v = ((h₀ ^ 3) ^ q) (h₀ v) := fun v => by
    rw [hh, hq, pow_succ, pow_mul, LinearEquiv.mul_apply]
  have hh2 : h (omegaInvNil s x₂) = omegaInvNil s x₃ := by
    rw [hpow, f2, omegaPlane_pow_apply_of_apply_eq g3]
  have hh3 : h (omegaInvNil s x₃) = omegaInvNil s x₁ := by
    rw [hpow, f3, omegaPlane_pow_apply_of_apply_eq g1]
  have hr : ∀ z, reflect Q (omegaInvNil s z) * s = s * reflect Q (omegaInvNil s z) := fun z =>
    reflect_mul_comm_of_mem_omegaInvSpace hs hss (omegaInvNil_mem_omegaInvSpace s z)
  have hgO : reflect Q (omegaInvNil s x₂) * reflect Q (omegaInvNil s x₃) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (reflect_mem_orthogonalGroup Q _) (reflect_mem_orthogonalGroup Q _)
  have hgs : reflect Q (omegaInvNil s x₂) * reflect Q (omegaInvNil s x₃) ∈
      Subgroup.centralizer ({s} : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.mul_left (hr x₂) (hr x₃)
  have hc := commutatorElement_mem_omegaO2Cent hhΩ hhs hho hgO hgs
  have c31 : reflect Q (omegaInvNil s x₃) * reflect Q (omegaInvNil s x₁) =
      reflect Q (omegaInvNil s x₁) * reflect Q (omegaInvNil s x₃) :=
    reflect_mul_comm_of_polar_eq_zero (polar_of_mem_omegaInvSpace hs hss
      (omegaInvNil_mem_omegaInvSpace s x₃) (omegaInvNil_mem_omegaInvSpace s x₁))
  have key : ⁅h, reflect Q (omegaInvNil s x₂) * reflect Q (omegaInvNil s x₃)⁆ =
      reflect Q (omegaInvNil s x₁) * reflect Q (omegaInvNil s x₂) := by
    rw [commutatorElement_def, show h * (reflect Q (omegaInvNil s x₂) *
        reflect Q (omegaInvNil s x₃)) * h⁻¹ = (h * reflect Q (omegaInvNil s x₂) * h⁻¹) *
        (h * reflect Q (omegaInvNil s x₃) * h⁻¹) by group, reflect_conj hhO, reflect_conj hhO,
      hh2, hh3, mul_inv_rev, reflect_inv, reflect_inv, c31]
    calc reflect Q (omegaInvNil s x₁) * reflect Q (omegaInvNil s x₃) *
          (reflect Q (omegaInvNil s x₃) * reflect Q (omegaInvNil s x₂)) =
        reflect Q (omegaInvNil s x₁) * (reflect Q (omegaInvNil s x₃) *
          reflect Q (omegaInvNil s x₃)) * reflect Q (omegaInvNil s x₂) := by
          simp only [mul_assoc]
      _ = _ := by rw [reflect_mul_self, mul_one]
  rw [← key]
  exact hc

end CFSG.SeitzReduction.SymplecticPilot
