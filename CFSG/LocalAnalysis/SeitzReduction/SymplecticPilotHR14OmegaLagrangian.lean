module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaPlane

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_reflect_pair [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) {x y : V}
    (hxy : polar Q x y = 1) :
    ∃ a b : V, a ∈ Submodule.span K {x, y} ∧ b ∈ Submodule.span K {x, y} ∧ Q a ≠ 0 ∧ Q b ≠ 0 ∧
      (∀ z, polar Q x z = 0 → polar Q y z = 0 → polar Q a z = 0 ∧ polar Q b z = 0) ∧
      ∀ v ∈ Submodule.span K {x, y}, reflect Q a (reflect Q b v) = v → v = 0 := by
  have h2 : (2 : K) = 0 := omegaInv_two_eq_zero
  have h11 : polar Q x x = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have h22 : polar Q y y = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have h21 : polar Q y x = 1 := by rw [polar_comm, hxy]
  obtain ⟨c₁, c₂, hc, hQ₁, hQ₂⟩ := omegaPlane_exists_two_nonzero hK (Q x) (Q y)
  have hQc : ∀ c : K, Q (x + c • y) = Q x + c + c ^ 2 * Q y := fun c => by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, hxy]
    ring
  have hQa : Q (x + c₁ • y) ≠ 0 := by rw [hQc]; exact hQ₁
  have hQb : Q (x + c₂ • y) ≠ 0 := by rw [hQc]; exact hQ₂
  have hpa : ∀ z, polar Q (x + c₁ • y) z = polar Q x z + c₁ * polar Q y z := fun z => by
    rw [polar_add_left, polar_smul_left_eq]
  have hpb : ∀ z, polar Q (x + c₂ • y) z = polar Q x z + c₂ * polar Q y z := fun z => by
    rw [polar_add_left, polar_smul_left_eq]
  have hxP : x ∈ Submodule.span K {x, y} := Submodule.subset_span (by simp)
  have hyP : y ∈ Submodule.span K {x, y} := Submodule.subset_span (by simp)
  refine ⟨x + c₁ • y, x + c₂ • y, Submodule.add_mem _ hxP (Submodule.smul_mem _ _ hyP),
    Submodule.add_mem _ hxP (Submodule.smul_mem _ _ hyP), hQa, hQb, fun z hz1 hz2 => ?_, ?_⟩
  · rw [hpa, hpb, hz1, hz2]
    simp
  intro v hv hfv
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hv
  have hrr : ∀ w z, reflect Q w (reflect Q w z) = z := fun w z => by
    rw [← LinearEquiv.mul_apply, reflect_mul_self]
    rfl
  set v := α • x + β • y with hv'
  have hba : reflect Q (x + c₂ • y) v = reflect Q (x + c₁ • y) v := by
    calc reflect Q (x + c₂ • y) v =
        reflect Q (x + c₁ • y) (reflect Q (x + c₁ • y) (reflect Q (x + c₂ • y) v)) :=
          (hrr _ _).symm
      _ = reflect Q (x + c₁ • y) v := by rw [hfv]
  rw [reflect_apply hQb, reflect_apply hQa] at hba
  have hmn := sub_right_inj.1 hba
  have e2 := congrArg (fun z => polar Q y z) hmn
  have e1 := congrArg (fun z => polar Q x z) hmn
  simp only [polar_smul_right_eq, polar_add_right, h11, h21, h22, hxy, mul_zero, mul_one,
    add_zero, zero_add] at e1 e2
  rw [e2] at e1
  have hν : polar Q (x + c₁ • y) v / Q (x + c₁ • y) = 0 := by
    have e : (polar Q (x + c₁ • y) v / Q (x + c₁ • y)) * (c₁ - c₂) = 0 := by
      linear_combination -e1
    exact (mul_eq_zero.1 e).resolve_right (sub_ne_zero.2 hc)
  rw [hν] at e2
  have hav : polar Q (x + c₁ • y) v = 0 := (div_eq_zero_iff.1 hν).resolve_right hQa
  have hbv : polar Q (x + c₂ • y) v = 0 := (div_eq_zero_iff.1 e2).resolve_right hQb
  rw [hpa] at hav
  rw [hpb] at hbv
  have h2v : polar Q y v = 0 := by
    have e : (c₁ - c₂) * polar Q y v = 0 := by linear_combination hav - hbv
    exact (mul_eq_zero.1 e).resolve_left (sub_ne_zero.2 hc)
  rw [h2v, mul_zero, add_zero] at hav
  rw [hv', polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h11, hxy] at hav
  rw [hv', polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h21, h22] at h2v
  have hβ : β = 0 := by linear_combination hav
  have hα : α = 0 := by linear_combination h2v
  rw [hv', hα, hβ, zero_smul, zero_smul, add_zero]

theorem reflect_mul_comm_of_polar_eq_zero {a a' : V} (h : polar Q a a' = 0) :
    reflect Q a * reflect Q a' = reflect Q a' * reflect Q a := by
  have e := reflect_conj (reflect_mem_orthogonalGroup Q a) a'
  rw [reflect_apply_of_polar_eq_zero h] at e
  calc reflect Q a * reflect Q a' = (reflect Q a * reflect Q a' * (reflect Q a)⁻¹) * reflect Q a :=
        by group
    _ = reflect Q a' * reflect Q a := by rw [e]

theorem eichler_mem_omegaO2Cent_of_doubled [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : 4 ≤ Nat.card K) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {x y : V}
    (hxy : polar Q x y = 1) (hxNy : polar Q x (omegaInvNil s y) = 1)
    (hNx : Q (omegaInvNil s x) = 0) (hNy : Q (omegaInvNil s y) = 0) {u : V}
    (hu : u ∈ omegaInvSpace s) (hux : polar Q u x = 0) (huy : polar Q u y = 0) :
    eichler Q u (omegaInvNil s x) ∈ omegaO2Cent Q s := by
  have h2 : (2 : K) = 0 := omegaInv_two_eq_zero
  obtain ⟨a, b, haP, hbP, hQa, hQb, habz, hfix⟩ := exists_reflect_pair hK hxy
  set P := Submodule.span K {x, y} with hP
  have hxP : x ∈ P := Submodule.subset_span (by simp)
  have hyP : y ∈ P := Submodule.subset_span (by simp)
  have h11 : polar Q x x = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have h22 : polar Q y y = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hyx : polar Q y x = 1 := by rw [polar_comm, hxy]
  have hNxy : polar Q (omegaInvNil s x) y = 1 := by rw [polar_omegaInvNil_left hs hss, hxNy]
  have hNyx : polar Q (omegaInvNil s y) x = 1 := by rw [polar_comm, hxNy]
  have hNxx : polar Q (omegaInvNil s x) x = 0 := by rw [polar_comm, ← map_omegaInvNil hs, hNx]
  have hNyy : polar Q (omegaInvNil s y) y = 0 := by rw [polar_comm, ← map_omegaInvNil hs, hNy]
  have hsv : ∀ v, s v = v + omegaInvNil s v := fun v => by
    rw [omegaInvNil_apply]
    abel
  have hsPP : ∀ v ∈ P, ∀ w ∈ P, polar Q (s v) w = 0 := by
    intro v hv w hw
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hv
    obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.1 hw
    rw [hsv, map_add, map_smul, map_smul]
    simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, h11, h22,
      hxy, hyx, hNxy, hNyx, hNxx, hNyy]
    linear_combination (α * δ + β * γ) * h2
  have hO : ∀ v, reflect Q v ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    reflect_mem_orthogonalGroup Q
  have hss' : ∀ v, s (s v) = v := omegaInv_apply_apply_of_mul_self hss
  have hc : ∀ v ∈ P, ∀ w ∈ P, reflect Q v * reflect Q (s w) = reflect Q (s w) * reflect Q v :=
    fun v hv w hw => reflect_mul_comm_of_polar_eq_zero (by rw [polar_comm]; exact hsPP w hw v hv)
  set g := reflect Q a * reflect Q b with hg
  set g' := reflect Q (s a) * reflect Q (s b) with hg'
  have hgg' : g * g' = g' * g := by
    have h1 : Commute (reflect Q a) g' :=
      (Commute.mul_right (hc a haP a haP) (hc a haP b hbP))
    have h2' : Commute (reflect Q b) g' :=
      (Commute.mul_right (hc b hbP a haP) (hc b hbP b hbP))
    exact (h1.mul_left h2').eq
  have hsg : s * g * s⁻¹ = g' := by
    rw [hg, hg', show s * (reflect Q a * reflect Q b) * s⁻¹ =
      (s * reflect Q a * s⁻¹) * (s * reflect Q b * s⁻¹) by group, reflect_conj hs, reflect_conj hs]
  have hsg' : s * g' * s⁻¹ = g := by
    rw [hg, hg', show s * (reflect Q (s a) * reflect Q (s b)) * s⁻¹ =
      (s * reflect Q (s a) * s⁻¹) * (s * reflect Q (s b) * s⁻¹) by group, reflect_conj hs,
      reflect_conj hs, hss', hss']
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : V ≃ₗ[K] V, h₀ = g * g' := ⟨_, rfl⟩
  have hh₀s : s * h₀ = h₀ * s := by
    have e : s * h₀ * s⁻¹ = h₀ := by
      rw [hh₀, show s * (g * g') * s⁻¹ = (s * g * s⁻¹) * (s * g' * s⁻¹) by group, hsg, hsg',
        hgg']
    calc s * h₀ = (s * h₀ * s⁻¹) * s := by group
      _ = h₀ * s := by rw [e]
  have hsq : h₀ ^ 2 ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    have e : h₀ ^ 2 = ⁅reflect Q a, reflect Q b⁆ * ⁅reflect Q (s a), reflect Q (s b)⁆ := by
      rw [hh₀, (Commute.mul_pow hgg' 2), _root_.sq, _root_.sq, commutatorElement_def,
        commutatorElement_def, reflect_inv, reflect_inv, reflect_inv, reflect_inv, hg, hg']
      simp only [mul_assoc]
    rw [e]
    exact mul_mem (Subgroup.commutator_mem_commutator (hO a) (hO b))
      (Subgroup.commutator_mem_commutator (hO _) (hO _))
  have : Finite (V ≃ₗ[K] V) := omegaPlane_finite_linearEquiv
  have hm0 : orderOf h₀ ≠ 0 := (isOfFinOrder_of_finite h₀).orderOf_pos.ne'
  obtain ⟨k, m, hm, hmk⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  set h := h₀ ^ 2 ^ k with hh
  have hord : orderOf h = m := by
    rw [hh, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hmk ▸ dvd_mul_right _ _), hmk,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hhsq : h ^ 2 ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [hh, ← pow_mul, mul_comm, pow_mul]
    exact pow_mem hsq _
  have hhΩ : h ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    obtain ⟨j, hj⟩ := hm
    have e : h = (h ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = m + 1 by omega, pow_succ, ← hord, pow_orderOf_eq_one,
        one_mul]
    rw [e]
    exact pow_mem hhsq _
  have hhs : h ∈ Subgroup.centralizer ({s} : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Commute.pow_right hh₀s (2 ^ k)).eq).symm
  have hsu : s u = u := apply_of_mem_omegaInvSpace hss hu
  have hhu : h u = u := by
    obtain ⟨hau, hbu⟩ := habz u (by rw [polar_comm]; exact hux) (by rw [polar_comm]; exact huy)
    have hsau : polar Q (s a) u = 0 := by rw [← hsu, polar_map_of_mem hs]; exact hau
    have hsbu : polar Q (s b) u = 0 := by rw [← hsu, polar_map_of_mem hs]; exact hbu
    have h0u : h₀ u = u := by
      rw [hh₀, hg, hg', LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        reflect_apply_of_polar_eq_zero hsbu, reflect_apply_of_polar_eq_zero hsau,
        reflect_apply_of_polar_eq_zero hbu, reflect_apply_of_polar_eq_zero hau]
    exact omegaPlane_pow_apply_of_apply_eq h0u _
  have hrP : ∀ w ∈ P, ∀ v ∈ P, reflect Q w v ∈ P := fun w hw v hv => by
    by_cases hQw : Q w = 0
    · rw [reflect_of_map_eq_zero hQw]
      exact hv
    · rw [reflect_apply hQw]
      exact P.sub_mem hv (P.smul_mem _ hw)
  have hgP : ∀ v ∈ P, g v ∈ P := fun v hv => by
    rw [hg, LinearEquiv.mul_apply]
    exact hrP a haP _ (hrP b hbP v hv)
  have hg'P : ∀ v ∈ P, g' v = v := fun v hv => by
    rw [hg', LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero (hsPP b hbP v hv),
      reflect_apply_of_polar_eq_zero (hsPP a haP v hv)]
  have hNh₀ : ∀ v, omegaInvNil s (h₀ v) = h₀ (omegaInvNil s v) := fun v => by
    rw [omegaInvNil_apply, omegaInvNil_apply, map_sub, ← LinearEquiv.mul_apply, hh₀s,
      LinearEquiv.mul_apply]
  have hh₀N : ∀ v ∈ P, h₀ (omegaInvNil s v) = omegaInvNil s (g v) := fun v hv => by
    rw [← hNh₀, hh₀, LinearEquiv.mul_apply, hg'P v hv]
  have hkerP : ∀ v ∈ P, omegaInvNil s v = 0 → v = 0 := by
    intro v hv hNv
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hv
    have e1 := congrArg (fun z => polar Q z x) hNv
    have e2 := congrArg (fun z => polar Q z y) hNv
    simp only [map_add, map_smul, polar_add_left, polar_smul_left_eq, hNxx, hNyx, hNxy, hNyy,
      polar_zero_left, mul_zero, mul_one, zero_add, add_zero] at e1 e2
    rw [e1, e2, zero_smul, zero_smul, add_zero]
  set NP := P.map (omegaInvNil s) with hNP
  have hh₀NP : ∀ w ∈ NP, h₀ w ∈ NP := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    rw [hh₀N v hv]
    exact Submodule.mem_map_of_mem (hgP v hv)
  have hfixNP : ∀ w ∈ NP, h₀ w = w → w = 0 := by
    intro w hw hfw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    rw [hh₀N v hv] at hfw
    have e : omegaInvNil s (g v - v) = 0 := by rw [map_sub, hfw, sub_self]
    have hgv := hkerP _ (P.sub_mem (hgP v hv) hv) e
    have hv0 := hfix v hv (by rw [← LinearEquiv.mul_apply, ← hg]; exact sub_eq_zero.1 hgv)
    rw [hv0, map_zero]
  have hhNP : ∀ w ∈ NP, h w ∈ NP := omegaPlane_pow_apply_mem_of_mapsTo hh₀NP _
  have hfixh : ∀ w ∈ NP, h w = w → w = 0 := omegaPlane_fpf_pow_two_pow hh₀NP hfixNP k
  set ψ : V →ₗ[K] V := (h : V →ₗ[K] V) - LinearMap.id with hψ
  have hψv : ∀ v, ψ v = h v - v := fun v => rfl
  have hmaps : ∀ v ∈ NP, ψ v ∈ NP := fun v hv => by
    rw [hψv]
    exact NP.sub_mem (hhNP v hv) hv
  set φ : NP →ₗ[K] NP := ψ.restrict hmaps with hφ
  have hφv : ∀ v : NP, (φ v : V) = h v - v := fun v => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply Subtype.ext
    have e := congrArg Subtype.val hv
    rw [hφv] at e
    exact hfixh v v.2 (sub_eq_zero.1 e)
  have hNxNP : omegaInvNil s x ∈ NP := Submodule.mem_map_of_mem hxP
  obtain ⟨v', hv'⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨omegaInvNil s x, hNxNP⟩
  have hv'eq : h v' - v' = omegaInvNil s x := by rw [← hφv, hv']
  have hv'W : (v' : V) ∈ omegaInvSpace s := by
    obtain ⟨z, -, hz⟩ := Submodule.mem_map.1 v'.2
    rw [← hz]
    exact omegaInvNil_mem_omegaInvSpace s z
  have hpuv : polar Q u v' = 0 := polar_of_mem_omegaInvSpace hs hss hu hv'W
  have hsv' : s v' = v' := apply_of_mem_omegaInvSpace hss hv'W
  have hEs : eichler Q u v' ∈ Subgroup.centralizer ({s} : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e := eichler_conj hs u v'
    rw [hsu, hsv'] at e
    symm
    calc s * eichler Q u v' = (s * eichler Q u v' * s⁻¹) * s := by group
      _ = eichler Q u v' * s := by rw [e]
  have hcm := commutatorElement_mem_omegaO2Cent hhΩ hhs (hord ▸ hm)
    (eichler_mem_orthogonalGroup Q u v') hEs
  rwa [commutatorElement_eichler (omega_le_orthogonalGroup hhΩ) hhu hpuv, hv'eq] at hcm

end CFSG.SeitzReduction.SymplecticPilot
