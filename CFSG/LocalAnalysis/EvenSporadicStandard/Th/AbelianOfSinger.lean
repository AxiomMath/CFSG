module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SingerAlt
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Matrix

theorem commute_of_singer_pairing {G : Type*} [Group G] {D Z A : Subgroup G}
    (θ : G → G) (c : G → (Fin 4 → ZMod 2)) (k : G) (j : ℕ)
    (hj : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 8)
    (hZD : Z ≤ D) (hZc : ∀ z ∈ Z, ∀ x ∈ D, z * x = x * z)
    (hsq : ∀ x ∈ D, x * x ∈ Z) (hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Z)
    (hΩ : ∀ z ∈ Z, z * z = 1 → z ∈ A)
    (hθmul : ∀ x ∈ D, ∀ y ∈ D, θ (x * y) = θ x * θ y) (hθA : ∀ x ∈ D, θ x ∈ A)
    (hθker : ∀ x ∈ D, θ x = 1 → x ∈ Z) (hθonto : ∀ a ∈ A, ∃ x ∈ D, θ x = a)
    (hkD : ∀ x ∈ D, k * x * k⁻¹ ∈ D) (hθk : ∀ x ∈ D, θ (k * x * k⁻¹) = k * θ x * k⁻¹)
    (hcmul : ∀ a ∈ A, ∀ b ∈ A, c (a * b) = c a + c b)
    (hcinj : ∀ a ∈ A, ∀ b ∈ A, c a = c b → a = b) (hconto : ∀ u, ∃ a ∈ A, c a = u)
    (hck : ∀ a ∈ A, c (k * a * k⁻¹) = (singerMat ^ j) *ᵥ c a) :
    ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
  classical
  have hθ1 : θ 1 = 1 := by
    have h := hθmul 1 D.one_mem 1 D.one_mem
    rw [mul_one] at h
    have h' : θ 1 * θ 1 = θ 1 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h'
  have hθinv : ∀ x ∈ D, θ x⁻¹ = (θ x)⁻¹ := by
    intro x hx
    apply eq_inv_of_mul_eq_one_left
    rw [← hθmul _ (D.inv_mem hx) _ hx, inv_mul_cancel, hθ1]
  have hc0 : c 1 = 0 := by
    have h := hcmul 1 A.one_mem 1 A.one_mem
    rw [mul_one] at h
    have h' : c 1 + c 1 = c 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have hker2 : ∀ x ∈ D, ∀ y ∈ D, θ x = θ y → ∃ z ∈ Z, x = y * z := by
    intro x hx y hy hxy
    refine ⟨y⁻¹ * x, hθker _ (D.mul_mem (D.inv_mem hy) hx) ?_, by group⟩
    rw [hθmul _ (D.inv_mem hy) _ hx, hθinv _ hy, hxy, inv_mul_cancel]
  have hcmA : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ A := by
    intro x hx y hy
    have hwZ : x * y * x⁻¹ * y⁻¹ ∈ Z := hcomm x hx y hy
    have hwc : (x * y * x⁻¹ * y⁻¹) * x = x * (x * y * x⁻¹ * y⁻¹) := hZc _ hwZ x hx
    have h1 : (x * x) * y * (x * x)⁻¹ * y⁻¹ =
        x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
    have h2 : (x * x) * y * (x * x)⁻¹ * y⁻¹ = 1 := by
      have := hZc (x * x) (hsq x hx) y hy
      calc (x * x) * y * (x * x)⁻¹ * y⁻¹ = (y * (x * x)) * (x * x)⁻¹ * y⁻¹ := by rw [this]
        _ = 1 := by group
    have h3 : x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) =
        (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by
      calc x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹)
          = ((x * y * x⁻¹ * y⁻¹) * x) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by rw [hwc]
        _ = (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
    exact hΩ _ hwZ (by rw [← h3, ← h1, h2])
  have hbi1 : ∀ x ∈ D, ∀ x' ∈ D, ∀ y ∈ D, (x * x') * y * (x * x')⁻¹ * y⁻¹ =
      (x' * y * x'⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by
    intro x hx x' hx' y hy
    have hc := hZc _ (hcomm x' hx' y hy) x hx
    calc (x * x') * y * (x * x')⁻¹ * y⁻¹
        = x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
      _ = ((x' * y * x'⁻¹ * y⁻¹) * x) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by rw [hc]
      _ = (x' * y * x'⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
  have hbi2 : ∀ x ∈ D, ∀ y ∈ D, ∀ y' ∈ D, x * (y * y') * x⁻¹ * (y * y')⁻¹ =
      (x * y * x⁻¹ * y⁻¹) * (x * y' * x⁻¹ * y'⁻¹) := by
    intro x hx y hy y' hy'
    have hc := hZc _ (hcomm x hx y' hy') y hy
    calc x * (y * y') * x⁻¹ * (y * y')⁻¹
        = (x * y * x⁻¹ * y⁻¹) * (y * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹) := by group
      _ = (x * y * x⁻¹ * y⁻¹) * (((x * y' * x⁻¹ * y'⁻¹) * y) * y⁻¹) := by rw [hc]
      _ = (x * y * x⁻¹ * y⁻¹) * (x * y' * x⁻¹ * y'⁻¹) := by group
  have hker_left : ∀ z ∈ Z, ∀ y ∈ D, z * y * z⁻¹ * y⁻¹ = 1 := by
    intro z hz y hy
    have := hZc z hz y hy
    calc z * y * z⁻¹ * y⁻¹ = (y * z) * z⁻¹ * y⁻¹ := by rw [← this]
      _ = 1 := by group
  have hker_right : ∀ x ∈ D, ∀ z ∈ Z, x * z * x⁻¹ * z⁻¹ = 1 := by
    intro x hx z hz
    have := hZc z hz x hx
    calc x * z * x⁻¹ * z⁻¹ = (z * x) * x⁻¹ * z⁻¹ := by rw [this]
      _ = 1 := by group
  have hcong1 : ∀ x₀ ∈ D, ∀ z ∈ Z, ∀ y ∈ D,
      (x₀ * z) * y * (x₀ * z)⁻¹ * y⁻¹ = x₀ * y * x₀⁻¹ * y⁻¹ := by
    intro x₀ hx₀ z hz y hy
    rw [hbi1 x₀ hx₀ z (hZD hz) y hy, hker_left z hz y hy, one_mul]
  have hcong2 : ∀ x ∈ D, ∀ y₀ ∈ D, ∀ z ∈ Z,
      x * (y₀ * z) * x⁻¹ * (y₀ * z)⁻¹ = x * y₀ * x⁻¹ * y₀⁻¹ := by
    intro x hx y₀ hy₀ z hz
    rw [hbi2 x hx y₀ hy₀ z (hZD hz), hker_right x hx z hz, mul_one]
  have hex : ∀ u : Fin 4 → ZMod 2, ∃ x ∈ D, c (θ x) = u := by
    intro u
    obtain ⟨a, haA, hau⟩ := hconto u
    obtain ⟨x, hxD, hxa⟩ := hθonto a haA
    exact ⟨x, hxD, by rw [hxa, hau]⟩
  choose σ hσD hσc using hex
  have hθσA : ∀ u, θ (σ u) ∈ A := fun u => hθA _ (hσD u)
  let β : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) := fun u v =>
    c (σ u * σ v * (σ u)⁻¹ * (σ v)⁻¹)
  have hβ1 : ∀ u u' v, β (u + u') v = β u v + β u' v := by
    intro u u' v
    have hθs : θ (σ (u + u')) = θ (σ u * σ u') := by
      apply hcinj _ (hθσA _) _ (hθA _ (D.mul_mem (hσD u) (hσD u')))
      rw [hσc, hθmul _ (hσD u) _ (hσD u'), hcmul _ (hθσA u) _ (hθσA u'), hσc, hσc]
    obtain ⟨z, hz, hzeq⟩ := hker2 _ (hσD (u + u')) _ (D.mul_mem (hσD u) (hσD u')) hθs
    have e1 : σ (u + u') * σ v * (σ (u + u'))⁻¹ * (σ v)⁻¹ =
        (σ u * σ u') * σ v * (σ u * σ u')⁻¹ * (σ v)⁻¹ := by
      rw [hzeq]
      exact hcong1 _ (D.mul_mem (hσD u) (hσD u')) z hz _ (hσD v)
    have e2 := hbi1 (σ u) (hσD u) (σ u') (hσD u') (σ v) (hσD v)
    show c (σ (u + u') * σ v * (σ (u + u'))⁻¹ * (σ v)⁻¹) =
      c (σ u * σ v * (σ u)⁻¹ * (σ v)⁻¹) + c (σ u' * σ v * (σ u')⁻¹ * (σ v)⁻¹)
    rw [e1, e2, hcmul _ (hcmA _ (hσD u') _ (hσD v)) _ (hcmA _ (hσD u) _ (hσD v)), add_comm]
  have hβ2 : ∀ u v v', β u (v + v') = β u v + β u v' := by
    intro u v v'
    have hθs : θ (σ (v + v')) = θ (σ v * σ v') := by
      apply hcinj _ (hθσA _) _ (hθA _ (D.mul_mem (hσD v) (hσD v')))
      rw [hσc, hθmul _ (hσD v) _ (hσD v'), hcmul _ (hθσA v) _ (hθσA v'), hσc, hσc]
    obtain ⟨z, hz, hzeq⟩ := hker2 _ (hσD (v + v')) _ (D.mul_mem (hσD v) (hσD v')) hθs
    have e1 : σ u * σ (v + v') * (σ u)⁻¹ * (σ (v + v'))⁻¹ =
        σ u * (σ v * σ v') * (σ u)⁻¹ * (σ v * σ v')⁻¹ := by
      rw [hzeq]
      exact hcong2 _ (hσD u) _ (D.mul_mem (hσD v) (hσD v')) z hz
    have e2 := hbi2 (σ u) (hσD u) (σ v) (hσD v) (σ v') (hσD v')
    show c (σ u * σ (v + v') * (σ u)⁻¹ * (σ (v + v'))⁻¹) =
      c (σ u * σ v * (σ u)⁻¹ * (σ v)⁻¹) + c (σ u * σ v' * (σ u)⁻¹ * (σ v')⁻¹)
    rw [e1, e2, hcmul _ (hcmA _ (hσD u) _ (hσD v)) _ (hcmA _ (hσD u) _ (hσD v'))]
  have hβal : ∀ u, β u u = 0 := by
    intro u
    show c (σ u * σ u * (σ u)⁻¹ * (σ u)⁻¹) = 0
    have : σ u * σ u * (σ u)⁻¹ * (σ u)⁻¹ = 1 := by group
    rw [this, hc0]
  have hβk : ∀ u v, β ((singerMat ^ j) *ᵥ u) ((singerMat ^ j) *ᵥ v) =
      (singerMat ^ j) *ᵥ β u v := by
    intro u v
    have hθσ : ∀ w, θ (σ ((singerMat ^ j) *ᵥ w)) = θ (k * σ w * k⁻¹) := by
      intro w
      apply hcinj _ (hθσA _) _ (hθA _ (hkD _ (hσD w)))
      rw [hσc, hθk _ (hσD w), hck _ (hθσA w), hσc]
    obtain ⟨z, hz, hze⟩ := hker2 _ (hσD ((singerMat ^ j) *ᵥ u)) _ (hkD _ (hσD u)) (hθσ u)
    obtain ⟨z', hz', hze'⟩ := hker2 _ (hσD ((singerMat ^ j) *ᵥ v)) _ (hkD _ (hσD v)) (hθσ v)
    have e1 : σ ((singerMat ^ j) *ᵥ u) * σ ((singerMat ^ j) *ᵥ v) *
        (σ ((singerMat ^ j) *ᵥ u))⁻¹ * (σ ((singerMat ^ j) *ᵥ v))⁻¹ =
        (k * σ u * k⁻¹) * (k * σ v * k⁻¹) * (k * σ u * k⁻¹)⁻¹ * (k * σ v * k⁻¹)⁻¹ := by
      rw [hze, hze']
      rw [hcong1 _ (hkD _ (hσD u)) z hz _ (D.mul_mem (hkD _ (hσD v)) (hZD hz')),
        hcong2 _ (hkD _ (hσD u)) _ (hkD _ (hσD v)) z' hz']
    have e2 : (k * σ u * k⁻¹) * (k * σ v * k⁻¹) * (k * σ u * k⁻¹)⁻¹ * (k * σ v * k⁻¹)⁻¹ =
        k * (σ u * σ v * (σ u)⁻¹ * (σ v)⁻¹) * k⁻¹ := by group
    show c (σ ((singerMat ^ j) *ᵥ u) * σ ((singerMat ^ j) *ᵥ v) *
        (σ ((singerMat ^ j) *ᵥ u))⁻¹ * (σ ((singerMat ^ j) *ᵥ v))⁻¹) =
      (singerMat ^ j) *ᵥ c (σ u * σ v * (σ u)⁻¹ * (σ v)⁻¹)
    rw [e1, e2]
    exact hck _ (hcmA _ (hσD u) _ (hσD v))
  have hzero := SingerAlt.singer_alt_eq_zero j hj β hβ1 hβ2 hβal hβk
  intro x hx y hy
  obtain ⟨z, hz, hxz⟩ := hker2 x hx (σ (c (θ x))) (hσD _)
    (hcinj _ (hθA _ hx) _ (hθσA _) (by rw [hσc]))
  obtain ⟨z', hz', hyz⟩ := hker2 y hy (σ (c (θ y))) (hσD _)
    (hcinj _ (hθA _ hy) _ (hθσA _) (by rw [hσc]))
  have hcm1 : x * y * x⁻¹ * y⁻¹ = 1 := by
    have h0 := hzero (c (θ x)) (c (θ y))
    have hA1 := hcmA _ (hσD (c (θ x))) _ (hσD (c (θ y)))
    have h1 : σ (c (θ x)) * σ (c (θ y)) * (σ (c (θ x)))⁻¹ * (σ (c (θ y)))⁻¹ = 1 :=
      hcinj _ hA1 _ A.one_mem (by rw [hc0]; exact h0)
    rw [hxz, hyz, hcong1 _ (hσD _) z hz _ (D.mul_mem (hσD _) (hZD hz')),
      hcong2 _ (hσD _) _ (hσD _) z' hz', h1]
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [hcm1, one_mul]

end CFSG.EvenSporadicStandard.ThStd
