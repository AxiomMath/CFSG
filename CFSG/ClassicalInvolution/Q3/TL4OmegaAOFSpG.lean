module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFGForm

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Gauss

section SpForm

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  [Module (GaussField F) V] [IsScalarTower F (GaussField F) V]
  {ω : LinearMap.BilinForm F V} {a : V ≃ₗ[F] V}

omit [IsScalarTower F (GaussField F) V] in
theorem omega_a_right (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hωa : ∀ u v, ω (a u) (a v) = -ω u v) (u v : V) : ω u (a v) = ω (a u) v := by
  have h := hωa (a u) v
  rw [a_a hω, map_neg, LinearMap.neg_apply] at h
  linear_combination -h

variable (ω) in
@[expose] noncomputable def spBilin (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hωa : ∀ u v, ω (a u) (a v) = -ω u v) : LinearMap.BilinForm (GaussField F) V :=
  LinearMap.mk₂ (GaussField F) (fun u v => (⟨ω u v, -ω (a u) v⟩ : GaussField F))
    (fun u₁ u₂ v => by
      ext
      · simp
      · simp
        ring)
    (fun z u v => by
      rw [smul_eq hω z u]
      ext
      · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          QuadraticAlgebra.re_mul]
        ring
      · simp only [map_add, map_smul, a_a hω, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
          LinearMap.neg_apply, smul_eq_mul, QuadraticAlgebra.im_mul]
        ring)
    (fun u v₁ v₂ => by
      ext
      · simp
      · simp
        ring)
    (fun z u v => by
      rw [smul_eq hω z v]
      ext
      · simp only [map_add, map_smul, omega_a_right hω hωa, smul_eq_mul, QuadraticAlgebra.re_mul]
        ring
      · simp only [map_add, map_smul, hωa, smul_eq_mul, QuadraticAlgebra.im_mul]
        ring)

theorem spBilin_apply (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hωa : ∀ u v, ω (a u) (a v) = -ω u v) (u v : V) :
    spBilin ω hω hωa u v = (⟨ω u v, -ω (a u) v⟩ : GaussField F) := rfl

theorem spBilin_self (h2 : (2 : F) ≠ 0)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hωa : ∀ u v, ω (a u) (a v) = -ω u v) (hskew : ∀ u v, ω u v = -ω v u) (v : V) :
    spBilin ω hω hωa v v = 0 := by
  have h1 : ω v v = 0 := by
    have := hskew v v
    have h3 : (2 : F) * ω v v = 0 := by linear_combination this
    exact (mul_eq_zero.mp h3).resolve_left h2
  have h4 : ω (a v) v = 0 := by
    have e1 := omega_a_right hω hωa v v
    have e2 := hskew v (a v)
    have h3 : (2 : F) * ω (a v) v = 0 := by linear_combination e2 - e1
    exact (mul_eq_zero.mp h3).resolve_left h2
  rw [spBilin_apply, h1, h4, neg_zero]
  rfl

theorem spBilin_skew (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hωa : ∀ u v, ω (a u) (a v) = -ω u v) (hskew : ∀ u v, ω u v = -ω v u) (u v : V) :
    spBilin ω hω hωa u v = -spBilin ω hω hωa v u := by
  rw [spBilin_apply, spBilin_apply]
  ext
  · simp [hskew u v]
  · simp only [QuadraticAlgebra.im_neg, neg_neg]
    rw [hskew (a u) v, omega_a_right hω hωa v u, neg_neg]

@[expose] noncomputable def ofCommute (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (ν : V ≃ₗ[F] V) (hc : ∀ v, ν (a v) = a (ν v)) : V ≃ₗ[GaussField F] V :=
  { ν with
    map_smul' := fun z v => by
      show ν (z • v) = z • ν v
      rw [smul_eq hω, smul_eq hω, map_add, map_smul, map_smul, hc] }

theorem ofCommute_apply (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (ν : V ≃ₗ[F] V) (hc : ∀ v, ν (a v) = a (ν v)) (v : V) : ofCommute hω ν hc v = ν v := rfl

theorem spBilin_map_iff (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hωa : ∀ u v, ω (a u) (a v) = -ω u v) {ν : V → V} (hc : ∀ v, ν (a v) = a (ν v)) :
    (∀ u v, ω (ν u) (ν v) = ω u v) ↔
      ∀ u v, spBilin ω hω hωa (ν u) (ν v) = spBilin ω hω hωa u v := by
  constructor
  · intro h u v
    rw [spBilin_apply, spBilin_apply, ← hc, h, h]
  · intro h u v
    have := congrArg QuadraticAlgebra.re (h u v)
    simpa [spBilin_apply] using this

end SpForm

end CFSG.ClassicalInvolution.Q3.TL4.Gauss
