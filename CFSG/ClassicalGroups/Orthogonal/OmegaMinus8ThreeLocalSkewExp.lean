module

public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def skewPair (Q : QuadraticForm K V) (u v : V) : V →ₗ[K] V where
  toFun x := polar Q x u • v - polar Q x v • u
  map_add' x y := by
    simp only [polar_add_left, add_smul]
    abel
  map_smul' c x := by
    simp only [polar_smul_left, smul_eq_mul, RingHom.id_apply]
    module

theorem skewPair_apply (u v x : V) :
    skewPair Q u v x = polar Q x u • v - polar Q x v • u :=
  rfl

theorem polar_skewPair_left (u v x y : V) :
    polar Q (skewPair Q u v x) y = - polar Q x (skewPair Q u v y) := by
  simp only [skewPair_apply, polar_sub_left, polar_smul_left, polar_sub_right, polar_smul_right,
    smul_eq_mul]
  rw [polar_comm Q v y, polar_comm Q u y, polar_comm Q y u, polar_comm Q y v]
  ring

theorem skewPair_map_apply {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (u v x : V) : skewPair Q (g u) (g v) (g x) = g (skewPair Q u v x) := by
  simp only [skewPair_apply, polar_map_of_mem hg, map_sub, map_smul]

private theorem polar_self_skew {ψ : V →ₗ[K] V} (h2 : (2 : K) ≠ 0)
    (hskew : ∀ x y, polar Q (ψ x) y = - polar Q x (ψ y)) (x : V) : polar Q x (ψ x) = 0 := by
  have h := hskew x x
  rw [polar_comm Q (ψ x) x] at h
  have : (2 : K) * polar Q x (ψ x) = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left h2

private theorem two_mul_map_skew {ψ : V →ₗ[K] V}
    (hskew : ∀ x y, polar Q (ψ x) y = - polar Q x (ψ y)) (x : V) :
    2 * Q (ψ x) = - polar Q x (ψ (ψ x)) := by
  rw [← polar_self_eq_two_mul, hskew]

@[expose] noncomputable def expSkew (ψ : V →ₗ[K] V) (h2 : (2 : K) ≠ 0)
    (hψ : ∀ x, ψ (ψ (ψ x)) = 0) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear
    (LinearMap.id + ψ + (2⁻¹ : K) • (ψ ∘ₗ ψ)) (LinearMap.id - ψ + (2⁻¹ : K) • (ψ ∘ₗ ψ))
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, map_add, map_sub, map_smul, hψ x, hψ (ψ x),
        map_zero, smul_zero, add_zero]
      match_scalars <;> field_simp <;> ring)
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, map_add, map_sub, map_smul, hψ x, hψ (ψ x),
        map_zero, smul_zero, add_zero]
      match_scalars <;> field_simp <;> ring)

theorem expSkew_apply (ψ : V →ₗ[K] V) (h2 : (2 : K) ≠ 0) (hψ : ∀ x, ψ (ψ (ψ x)) = 0) (x : V) :
    expSkew ψ h2 hψ x = x + ψ x + (2⁻¹ : K) • ψ (ψ x) :=
  rfl

theorem expSkew_inv_apply (ψ : V →ₗ[K] V) (h2 : (2 : K) ≠ 0) (hψ : ∀ x, ψ (ψ (ψ x)) = 0)
    (x : V) : (expSkew ψ h2 hψ)⁻¹ x = x - ψ x + (2⁻¹ : K) • ψ (ψ x) :=
  rfl

theorem expSkew_mem_orthogonalGroup {ψ : V →ₗ[K] V} (h2 : (2 : K) ≠ 0)
    (hψ : ∀ x, ψ (ψ (ψ x)) = 0) (hskew : ∀ x y, polar Q (ψ x) y = - polar Q x (ψ y)) :
    expSkew ψ h2 hψ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [expSkew_apply]
  have h1 : polar Q x (ψ x) = 0 := polar_self_skew h2 hskew x
  have h2' : 2 * Q (ψ x) = - polar Q x (ψ (ψ x)) := two_mul_map_skew hskew x
  have h3 : polar Q (ψ x) (ψ (ψ x)) = 0 := by
    rw [hskew, hψ, polar_zero_right, neg_zero]
  have h4 : 2 * Q (ψ (ψ x)) = 0 := by
    have := two_mul_map_skew hskew (ψ x)
    rw [hψ, polar_zero_right, neg_zero] at this
    exact this
  have h4' : Q (ψ (ψ x)) = 0 := (mul_eq_zero.1 h4).resolve_left h2
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, h1, map_smul_eq_sq, h4', polar_add_left,
    polar_smul_right_eq, polar_smul_right_eq, h3]
  field_simp
  linear_combination 2 * h2'

theorem expSkew_zpow (ψ : V →ₗ[K] V) (h2 : (2 : K) ≠ 0) (hψ : ∀ x, ψ (ψ (ψ x)) = 0) (k : ℤ)
    (x : V) :
    (expSkew ψ h2 hψ ^ k) x = x + (k : K) • ψ x + ((k : K) ^ 2 / 2) • ψ (ψ x) := by
  induction k using Int.induction_on generalizing x with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, LinearEquiv.mul_apply, ih, expSkew_apply]
    simp only [map_add, map_smul, hψ x, map_zero, smul_zero, add_zero]
    push_cast
    match_scalars <;> field_simp <;> ring
  | pred k ih =>
    rw [zpow_sub_one, LinearEquiv.mul_apply, ih, expSkew_inv_apply]
    simp only [map_add, map_sub, map_smul, hψ x, map_zero, smul_zero, add_zero]
    push_cast
    match_scalars <;> field_simp <;> ring

theorem expSkew_ne_one {ψ : V →ₗ[K] V} (h2 : (2 : K) ≠ 0) (hψ : ∀ x, ψ (ψ (ψ x)) = 0)
    (hne : ψ ≠ 0) : expSkew ψ h2 hψ ≠ 1 := by
  intro h
  apply hne
  refine LinearMap.ext fun x => ?_
  have h1 : ∀ y, ψ y + (2⁻¹ : K) • ψ (ψ y) = 0 := fun y => by
    have := congrArg (fun e => e y) h
    simp only [expSkew_apply] at this
    have h' : y + (ψ y + (2⁻¹ : K) • ψ (ψ y)) = y + 0 := by
      rw [add_zero, ← add_assoc]
      exact this
    exact add_left_cancel h'
  have h3 : ψ (ψ x) = 0 := by
    have := h1 (ψ x)
    rw [hψ x, smul_zero, add_zero] at this
    exact this
  have := h1 x
  rw [h3, smul_zero, add_zero] at this
  exact this

theorem orderOf_expSkew_of_charP {ψ : V →ₗ[K] V} (h2 : (2 : K) ≠ 0)
    (hψ : ∀ x, ψ (ψ (ψ x)) = 0) {p : ℕ} (hp : p.Prime) [CharP K p] (hne : ψ ≠ 0) :
    orderOf (expSkew ψ h2 hψ) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime ?_ (expSkew_ne_one h2 hψ hne)
  refine LinearEquiv.ext fun x => ?_
  have h := expSkew_zpow ψ h2 hψ (p : ℤ) x
  rw [zpow_natCast] at h
  rw [h]
  simp

theorem commute_expSkew_of_commute {ψ : V →ₗ[K] V} (h2 : (2 : K) ≠ 0)
    (hψ : ∀ x, ψ (ψ (ψ x)) = 0) {g : V ≃ₗ[K] V} (hg : ∀ x, ψ (g x) = g (ψ x)) :
    Commute (expSkew ψ h2 hψ) g := by
  refine LinearEquiv.ext fun x => ?_
  simp only [LinearEquiv.mul_apply, expSkew_apply, map_add, map_smul, hg]

theorem commute_expSkew_expSkew {ψ ψ' : V →ₗ[K] V} (h2 : (2 : K) ≠ 0)
    (hψ : ∀ x, ψ (ψ (ψ x)) = 0) (hψ' : ∀ x, ψ' (ψ' (ψ' x)) = 0)
    (hcomm : ∀ x, ψ (ψ' x) = ψ' (ψ x)) :
    Commute (expSkew ψ h2 hψ) (expSkew ψ' h2 hψ') := by
  refine commute_expSkew_of_commute h2 hψ fun x => ?_
  simp only [expSkew_apply, map_add, map_smul, hcomm]

theorem expSkew_not_mem_zpowers {ψ ψ' : V →ₗ[K] V} (h2 : (2 : K) ≠ 0)
    (hψ : ∀ x, ψ (ψ (ψ x)) = 0) (hψ' : ∀ x, ψ' (ψ' (ψ' x)) = 0)
    (hψ'2 : ∀ x, ψ' (ψ' x) = 0) (hψ'ne : ψ' ≠ 0) (hψ2 : ∃ x₀, ψ (ψ x₀) ≠ 0) :
    expSkew ψ' h2 hψ' ∉ Subgroup.zpowers (expSkew ψ h2 hψ) := by
  rintro ⟨k, hk⟩
  have h1 : ∀ x, ψ' x = (k : K) • ψ x + ((k : K) ^ 2 / 2) • ψ (ψ x) := fun x => by
    have := congrArg (fun e => e x) hk
    simp only [expSkew_zpow, expSkew_apply, hψ'2, smul_zero, add_zero] at this
    have h' : x + ψ' x = x + ((k : K) • ψ x + ((k : K) ^ 2 / 2) • ψ (ψ x)) := by
      rw [← this]
      abel
    exact add_left_cancel h'
  obtain ⟨x₀, hx₀⟩ := hψ2
  have h4 : (k : K) ^ 2 • ψ (ψ x₀) = 0 := by
    have h5 := hψ'2 x₀
    rw [h1 x₀, map_add, map_smul, map_smul, h1 (ψ x₀), h1 (ψ (ψ x₀))] at h5
    simp only [map_add, map_smul, hψ x₀, hψ (ψ x₀), map_zero, smul_zero, add_zero] at h5
    rw [smul_smul, ← _root_.sq] at h5
    exact h5
  have h6 : (k : K) = 0 := by
    rcases smul_eq_zero.1 h4 with h | h
    · exact (pow_eq_zero_iff two_ne_zero).1 h
    · exact absurd h hx₀
  apply hψ'ne
  refine LinearMap.ext fun x => ?_
  rw [h1 x, h6]
  simp

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
