module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaPlane

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_odd_of_polar_eq_one_of_coeff [Finite K] [CharP K 2] [FiniteDimensional K V]
    {p₁ p₂ : V} (h12 : polar Q p₁ p₂ = 1) {c₁ c₂ : K} (hc : c₁ ≠ c₂)
    (hQ₁ : Q p₁ + c₁ + c₁ ^ 2 * Q p₂ ≠ 0) (hQ₂ : Q p₁ + c₂ + c₂ ^ 2 * Q p₂ ≠ 0) :
    ∃ h : V ≃ₗ[K] V,
      h ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      Odd (orderOf h) ∧
      (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g p₁ = p₁ → g p₂ = p₂ → g * h = h * g) ∧
      (∀ x, polar Q p₁ x = 0 → polar Q p₂ x = 0 → h x = x) ∧
      ∃ α β : K, h (α • p₁ + β • p₂) - (α • p₁ + β • p₂) = p₁ := by
  have h2 : (2 : K) = 0 := omegaInv_two_eq_zero
  have h11 : polar Q p₁ p₁ = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have h22 : polar Q p₂ p₂ = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have h21 : polar Q p₂ p₁ = 1 := by rw [polar_comm, h12]
  have hQc : ∀ c : K, Q (p₁ + c • p₂) = Q p₁ + c + c ^ 2 * Q p₂ := fun c => by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, h12]
    ring
  set a := p₁ + c₁ • p₂ with ha
  set b := p₁ + c₂ • p₂ with hb
  have hQa : Q a ≠ 0 := by rw [ha, hQc]; exact hQ₁
  have hQb : Q b ≠ 0 := by rw [hb, hQc]; exact hQ₂
  have hpa : ∀ x, polar Q a x = polar Q p₁ x + c₁ * polar Q p₂ x := fun x => by
    rw [ha, polar_add_left, polar_smul_left_eq]
  have hpb : ∀ x, polar Q b x = polar Q p₁ x + c₂ * polar Q p₂ x := fun x => by
    rw [hb, polar_add_left, polar_smul_left_eq]
  have hp1a : polar Q p₁ a = c₁ := by
    rw [ha, polar_add_right, polar_smul_right_eq, h11, h12]; ring
  have hp1b : polar Q p₁ b = c₂ := by
    rw [hb, polar_add_right, polar_smul_right_eq, h11, h12]; ring
  have hp2a : polar Q p₂ a = 1 := by
    rw [ha, polar_add_right, polar_smul_right_eq, h21, h22]; ring
  have hp2b : polar Q p₂ b = 1 := by
    rw [hb, polar_add_right, polar_smul_right_eq, h21, h22]; ring
  have hO : ∀ v, reflect Q v ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    reflect_mem_orthogonalGroup Q
  have hrr : ∀ w y, reflect Q w (reflect Q w y) = y := fun w y => by
    rw [← LinearEquiv.mul_apply, reflect_mul_self]
    rfl
  set h₀ := reflect Q a * reflect Q b with hh₀
  set P : Submodule K V := Submodule.span K {p₁, p₂} with hP
  have hp₁P : p₁ ∈ P := Submodule.subset_span (by simp)
  have hp₂P : p₂ ∈ P := Submodule.subset_span (by simp)
  have haP : a ∈ P := P.add_mem hp₁P (P.smul_mem _ hp₂P)
  have hbP : b ∈ P := P.add_mem hp₁P (P.smul_mem _ hp₂P)
  have hrP : ∀ w ∈ P, ∀ v ∈ P, reflect Q w v ∈ P := fun w hw v hv => by
    by_cases hQw : Q w = 0
    · rw [reflect_of_map_eq_zero hQw]
      exact hv
    · rw [reflect_apply hQw]
      exact P.sub_mem hv (P.smul_mem _ hw)
  have hh₀P : ∀ v ∈ P, h₀ v ∈ P := fun v hv => by
    rw [hh₀, LinearEquiv.mul_apply]
    exact hrP a haP _ (hrP b hbP v hv)
  have hfix : ∀ v ∈ P, h₀ v = v → v = 0 := by
    intro v hv hfv
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hv
    set v := α • p₁ + β • p₂ with hv'
    rw [hh₀, LinearEquiv.mul_apply] at hfv
    have hba : reflect Q b v = reflect Q a v := by
      calc reflect Q b v = reflect Q a (reflect Q a (reflect Q b v)) := (hrr a _).symm
        _ = reflect Q a v := by rw [hfv]
    rw [reflect_apply hQb, reflect_apply hQa] at hba
    have hmn := sub_right_inj.1 hba
    have e2 := congrArg (fun y => polar Q p₂ y) hmn
    have e1 := congrArg (fun y => polar Q p₁ y) hmn
    simp only [polar_smul_right_eq, hp2a, hp2b, hp1a, hp1b, mul_one] at e1 e2
    rw [e2] at e1
    have hν : polar Q a v / Q a = 0 := by
      have e : (polar Q a v / Q a) * (c₁ - c₂) = 0 := by linear_combination -e1
      exact (mul_eq_zero.1 e).resolve_right (sub_ne_zero.2 hc)
    rw [hν] at e2
    have hav : polar Q a v = 0 := (div_eq_zero_iff.1 hν).resolve_right hQa
    have hbv : polar Q b v = 0 := (div_eq_zero_iff.1 e2).resolve_right hQb
    rw [hpa] at hav
    rw [hpb] at hbv
    have h2v : polar Q p₂ v = 0 := by
      have e : (c₁ - c₂) * polar Q p₂ v = 0 := by linear_combination hav - hbv
      exact (mul_eq_zero.1 e).resolve_left (sub_ne_zero.2 hc)
    rw [h2v, mul_zero, add_zero] at hav
    rw [hv', polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h11, h12] at hav
    rw [hv', polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h21, h22] at h2v
    have hβ : β = 0 := by linear_combination hav
    have hα : α = 0 := by linear_combination h2v
    rw [hv', hα, hβ, zero_smul, zero_smul, add_zero]
  have : Finite (V ≃ₗ[K] V) := omegaPlane_finite_linearEquiv
  have hm0 : orderOf h₀ ≠ 0 := (isOfFinOrder_of_finite h₀).orderOf_pos.ne'
  obtain ⟨k, m, hm, hmk⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  set h := h₀ ^ 2 ^ k with hh
  have hord : orderOf h = m := by
    rw [hh, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hmk ▸ dvd_mul_right _ _), hmk,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hsq : h₀ * h₀ = ⁅reflect Q a, reflect Q b⁆ := by
    rw [commutatorElement_def, reflect_inv, reflect_inv, hh₀]
    simp only [mul_assoc]
  have hh₀sq : h₀ ^ 2 ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [_root_.sq, hsq]
    exact Subgroup.commutator_mem_commutator (hO a) (hO b)
  have hhsq : h ^ 2 ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [hh, ← pow_mul, mul_comm, pow_mul]
    exact pow_mem hh₀sq _
  have hhΩ : h ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    obtain ⟨j, hj⟩ := hm
    have e : h = (h ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = m + 1 by omega, pow_succ, ← hord, pow_orderOf_eq_one,
        one_mul]
    rw [e]
    exact pow_mem hhsq _
  have hcomm : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g p₁ = p₁ → g p₂ = p₂ →
      g * h = h * g := by
    intro g hg hg1 hg2
    have hcr : ∀ w, g w = w → Commute g (reflect Q w) := fun w hw => by
      have e := reflect_conj hg w
      rw [hw] at e
      show g * reflect Q w = reflect Q w * g
      calc g * reflect Q w = (g * reflect Q w * g⁻¹) * g := by group
        _ = reflect Q w * g := by rw [e]
    have hga : g a = a := by rw [ha, map_add, map_smul, hg1, hg2]
    have hgb : g b = b := by rw [hb, map_add, map_smul, hg1, hg2]
    exact (((hcr a hga).mul_right (hcr b hgb)).pow_right _).eq
  have hfixx : ∀ x, polar Q p₁ x = 0 → polar Q p₂ x = 0 → h x = x := by
    intro x hx1 hx2
    have hxa : polar Q a x = 0 := by rw [hpa, hx1, hx2, mul_zero, add_zero]
    have hxb : polar Q b x = 0 := by rw [hpb, hx1, hx2, mul_zero, add_zero]
    have h0x : h₀ x = x := by
      rw [hh₀, LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero hxb,
        reflect_apply_of_polar_eq_zero hxa]
    exact omegaPlane_pow_apply_of_apply_eq h0x _
  have hhP : ∀ v ∈ P, h v ∈ P := omegaPlane_pow_apply_mem_of_mapsTo hh₀P _
  have hfixh : ∀ v ∈ P, h v = v → v = 0 := omegaPlane_fpf_pow_two_pow hh₀P hfix k
  set ψ : V →ₗ[K] V := (h : V →ₗ[K] V) - LinearMap.id with hψ
  have hψv : ∀ v, ψ v = h v - v := fun v => rfl
  have hmaps : ∀ v ∈ P, ψ v ∈ P := fun v hv => by
    rw [hψv]
    exact P.sub_mem (hhP v hv) hv
  set φ : P →ₗ[K] P := ψ.restrict hmaps with hφ
  have hφv : ∀ v : P, (φ v : V) = h v - v := fun v => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply Subtype.ext
    have e := congrArg Subtype.val hv
    rw [hφv] at e
    exact hfixh v v.2 (sub_eq_zero.1 e)
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨p₁, hp₁P⟩
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 v.2
  refine ⟨h, hhΩ, hord ▸ hm, hcomm, hfixx, α, β, ?_⟩
  rw [hαβ, ← hφv, hv]

theorem exists_odd_of_polar_eq_one_two [Finite K] [CharP K 2] [FiniteDimensional K V]
    {p₁ p₂ : V} (h12 : polar Q p₁ p₂ = 1) (h1 : Q p₁ ≠ 0) (h2 : Q (p₁ + p₂) ≠ 0) :
    ∃ h : V ≃ₗ[K] V,
      h ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      Odd (orderOf h) ∧
      (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g p₁ = p₁ → g p₂ = p₂ → g * h = h * g) ∧
      (∀ x, polar Q p₁ x = 0 → polar Q p₂ x = 0 → h x = x) ∧
      ∃ α β : K, h (α • p₁ + β • p₂) - (α • p₁ + β • p₂) = p₁ := by
  refine exists_odd_of_polar_eq_one_of_coeff h12 (c₁ := 0) (c₂ := 1) zero_ne_one ?_ ?_
  · rw [zero_pow two_ne_zero, zero_mul, add_zero, add_zero]
    exact h1
  · have e : Q (p₁ + p₂) = Q p₁ + 1 + 1 ^ 2 * Q p₂ := by
      rw [QuadraticMap.map_add Q, h12]
      ring
    rw [← e]
    exact h2

theorem eichler_mem_omegaO2Cent_of_plane_two [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {u : V}
    (hu : u ∈ omegaInvSpace s) {p₁ p₂ : V} (hp₁ : omegaInvNil s p₁ = 0)
    (hp₂ : omegaInvNil s p₂ = 0) (h12 : polar Q p₁ p₂ = 1) (h1 : Q p₁ ≠ 0)
    (h2 : Q (p₁ + p₂) ≠ 0) : eichler Q u p₁ ∈ omegaO2Cent Q s := by
  obtain ⟨h, hΩ, hodd, hcomm, hfixx, α, β, hαβ⟩ := exists_odd_of_polar_eq_one_two h12 h1 h2
  have hs1 : s p₁ = p₁ := omegaInvNil_eq_zero_iff_apply.1 hp₁
  have hs2 : s p₂ = p₂ := omegaInvNil_eq_zero_iff_apply.1 hp₂
  have hhs : h ∈ Subgroup.centralizer ({s} : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm s hs hs1 hs2).symm
  have hpu : ∀ p, omegaInvNil s p = 0 → polar Q p u = 0 := fun p hp =>
    (omegaInvNil_eq_zero_iff hQ hs hss).1 hp u hu
  have hhu : h u = u := hfixx u (hpu p₁ hp₁) (hpu p₂ hp₂)
  set v := α • p₁ + β • p₂ with hv
  have hpv : polar Q u v = 0 := by
    rw [hv, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_comm Q u p₁,
      polar_comm Q u p₂, hpu p₁ hp₁, hpu p₂ hp₂]
    ring
  have hsv : s v = v := by rw [hv, map_add, map_smul, map_smul, hs1, hs2]
  have hsu : s u = u := apply_of_mem_omegaInvSpace hss hu
  have hEs : eichler Q u v ∈ Subgroup.centralizer ({s} : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e := eichler_conj hs u v
    rw [hsu, hsv] at e
    symm
    calc s * eichler Q u v = (s * eichler Q u v * s⁻¹) * s := by group
      _ = eichler Q u v * s := by rw [e]
  have hc := commutatorElement_mem_omegaO2Cent hΩ hhs hodd (eichler_mem_orthogonalGroup Q u v)
    hEs
  rwa [commutatorElement_eichler (omega_le_orthogonalGroup hΩ) hhu hpv, hαβ] at hc

end CFSG.SeitzReduction.SymplecticPilot
