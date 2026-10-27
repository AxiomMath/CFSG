module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaClasses
public import CFSG.ClassicalGroups.Orthogonal.Derived

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def omegaO2Cent (Q : QuadraticForm K V) (s : V ≃ₗ[K] V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {x | x ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
    TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧ x ∈ Subgroup.centralizer ({s} : Set (V ≃ₗ[K] V)) ∧
      Odd (orderOf x)}

theorem omega_le_orthogonalGroup :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      TauCeti.QuadraticMap.orthogonalGroup Q :=
  Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem omega_conj_mem_of_orthogonalGroup {g x : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx : x ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    g * x * g⁻¹ ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have h : g * x * g⁻¹ = ⁅g, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [h]
  exact mul_mem (Subgroup.commutator_mem_commutator hg (omega_le_orthogonalGroup hx)) hx

theorem commutatorElement_mem_omegaO2Cent {s h g : V ≃ₗ[K] V}
    (hh : h ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hhs : h ∈ Subgroup.centralizer ({s} : Set (V ≃ₗ[K] V))) (hho : Odd (orderOf h))
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgs : g ∈ Subgroup.centralizer ({s} : Set (V ≃ₗ[K] V))) :
    ⁅h, g⁆ ∈ omegaO2Cent Q s := by
  have e : ⁅h, g⁆ = h * (g * h⁻¹ * g⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  refine mul_mem (Subgroup.subset_closure ⟨hh, hhs, hho⟩) (Subgroup.subset_closure ⟨?_, ?_, ?_⟩)
  · exact omega_conj_mem_of_orthogonalGroup hg (inv_mem hh)
  · exact mul_mem (mul_mem hgs (inv_mem hhs)) (inv_mem hgs)
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_inv]
    exact hho

theorem omegaPlane_exists_two_nonzero [Finite K] (hK : 4 ≤ Nat.card K) (A B : K) :
    ∃ c₁ c₂ : K, c₁ ≠ c₂ ∧ A + c₁ + c₁ ^ 2 * B ≠ 0 ∧ A + c₂ + c₂ ^ 2 * B ≠ 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hroots : (Finset.univ.filter fun c : K => A + c + c ^ 2 * B = 0).card ≤ 2 := by
    by_contra h
    push Not at h
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
    have h1 : 1 + (a + b) * B = 0 := by
      have e : (a - b) * (1 + (a + b) * B) = 0 := by linear_combination ha - hb
      exact (mul_eq_zero.1 e).resolve_left (sub_ne_zero.2 hab)
    have h2 : 1 + (a + c) * B = 0 := by
      have e : (a - c) * (1 + (a + c) * B) = 0 := by linear_combination ha - hc
      exact (mul_eq_zero.1 e).resolve_left (sub_ne_zero.2 hac)
    have hB : B = 0 := by
      have e : (b - c) * B = 0 := by linear_combination h1 - h2
      exact (mul_eq_zero.1 e).resolve_left (sub_ne_zero.2 hbc)
    rw [hB, mul_zero, add_zero] at h1
    exact one_ne_zero h1
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset K))
    (fun c : K => A + c + c ^ 2 * B = 0)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hsum
  obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := Finset.one_lt_card.1
    (show 1 < (Finset.univ.filter fun c : K => ¬A + c + c ^ 2 * B = 0).card by omega)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
  exact ⟨c₁, c₂, hne, hc₁, hc₂⟩

theorem omegaPlane_fpf_mul_self [CharP K 2] {P : Submodule K V} {g : V ≃ₗ[K] V}
    (hgP : ∀ v ∈ P, g v ∈ P) (hfix : ∀ v ∈ P, g v = v → v = 0) :
    ∀ v ∈ P, (g * g) v = v → v = 0 := by
  intro v hv h
  have hw : g v - v ∈ P := P.sub_mem (hgP v hv) hv
  have hgw : g (g v - v) = g v - v := by
    rw [map_sub, ← LinearEquiv.mul_apply, h, omegaInv_sub_eq_add K, omegaInv_sub_eq_add K,
      add_comm]
  exact hfix v hv (sub_eq_zero.1 (hfix _ hw hgw))

theorem omegaPlane_pow_apply_mem_of_mapsTo {P : Submodule K V} {g : V ≃ₗ[K] V}
    (hgP : ∀ v ∈ P, g v ∈ P) (m : ℕ) : ∀ v ∈ P, (g ^ m) v ∈ P := by
  induction m with
  | zero => intro v hv; simpa using hv
  | succ m ih =>
    intro v hv
    rw [pow_succ, LinearEquiv.mul_apply]
    exact ih _ (hgP v hv)

theorem omegaPlane_pow_apply_of_apply_eq {g : V ≃ₗ[K] V} {x : V} (hx : g x = x) (m : ℕ) :
    (g ^ m) x = x := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, LinearEquiv.mul_apply, hx, ih]

theorem omegaPlane_fpf_pow_two_pow [CharP K 2] {P : Submodule K V} {g : V ≃ₗ[K] V}
    (hgP : ∀ v ∈ P, g v ∈ P) (hfix : ∀ v ∈ P, g v = v → v = 0) (k : ℕ) :
    ∀ v ∈ P, (g ^ 2 ^ k) v = v → v = 0 := by
  induction k with
  | zero => simpa using hfix
  | succ k ih =>
    rw [pow_succ, pow_mul, _root_.sq]
    exact omegaPlane_fpf_mul_self (omegaPlane_pow_apply_mem_of_mapsTo hgP _) ih

theorem omegaPlane_finite_linearEquiv [Finite K] [FiniteDimensional K V] : Finite (V ≃ₗ[K] V) := by
  have : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) fun g g' h =>
    LinearEquiv.ext (congrFun h)

theorem exists_odd_of_polar_eq_one [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : 4 ≤ Nat.card K) {p₁ p₂ : V} (h12 : polar Q p₁ p₂ = 1) :
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
  obtain ⟨c₁, c₂, hc, hQ₁, hQ₂⟩ := omegaPlane_exists_two_nonzero hK (Q p₁) (Q p₂)
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

theorem eichler_mem_omegaO2Cent_of_plane [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {u : V}
    (hu : u ∈ omegaInvSpace s) {p₁ p₂ : V} (hp₁ : omegaInvNil s p₁ = 0)
    (hp₂ : omegaInvNil s p₂ = 0) (h12 : polar Q p₁ p₂ = 1) :
    eichler Q u p₁ ∈ omegaO2Cent Q s := by
  obtain ⟨h, hΩ, hodd, hcomm, hfixx, α, β, hαβ⟩ := exists_odd_of_polar_eq_one hK h12
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

theorem eichler_mem_omegaO2Cent [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hl : 2 * finrank K (omegaInvSpace s) < finrank K V) {u : V} (hu : u ∈ omegaInvSpace s)
    {z : V} (hz : omegaInvNil s z = 0) : eichler Q u z ∈ omegaO2Cent Q s := by
  have hpu : ∀ p, omegaInvNil s p = 0 → polar Q u p = 0 := fun p hp => by
    rw [polar_comm]
    exact (omegaInvNil_eq_zero_iff hQ hs hss).1 hp u hu
  have hout : ∀ z, omegaInvNil s z = 0 → z ∉ omegaInvSpace s →
      eichler Q u z ∈ omegaO2Cent Q s := by
    intro z hz hzW
    obtain ⟨z', hz', hzz'⟩ : ∃ z', omegaInvNil s z' = 0 ∧ polar Q z z' ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hzW (mem_omegaInvSpace_of_forall_polar hQ hs hss hc)
    refine eichler_mem_omegaO2Cent_of_plane hK hQ hs hss hu hz
      (p₂ := (polar Q z z')⁻¹ • z') ?_ ?_
    · rw [map_smul, hz', smul_zero]
    · rw [polar_smul_right_eq, inv_mul_cancel₀ hzz']
  by_cases hzW : z ∈ omegaInvSpace s
  ·
    obtain ⟨e, he, heW⟩ : ∃ e, omegaInvNil s e = 0 ∧ e ∉ omegaInvSpace s := by
      by_contra hc
      push Not at hc
      have hle : LinearMap.ker (omegaInvNil s) ≤ omegaInvSpace s := fun x hx =>
        hc x (LinearMap.mem_ker.1 hx)
      have h1 := Submodule.finrank_mono hle
      have h2 := LinearMap.finrank_range_add_finrank_ker (omegaInvNil s)
      change finrank K (omegaInvSpace s) + _ = _ at h2
      omega
    have hez : omegaInvNil s (e + z) = 0 := by rw [map_add, he, hz, add_zero]
    have hezW : e + z ∉ omegaInvSpace s := fun h => heW (by
      have := (omegaInvSpace s).sub_mem h hzW
      rwa [add_sub_cancel_right] at this)
    have hne : omegaInvNil s (-e) = 0 := by rw [map_neg, he, neg_zero]
    have hneW : -e ∉ omegaInvSpace s := fun h => heW (by simpa using (omegaInvSpace s).neg_mem h)
    have e1 := hout _ hez hezW
    have e2 := hout _ hne hneW
    have e3 := mul_mem e1 e2
    rwa [eichler_mul (hpu _ hez) (hpu _ hne), add_neg_cancel_comm] at e3
  · exact hout z hz hzW

end CFSG.SeitzReduction.SymplecticPilot
