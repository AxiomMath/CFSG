module

public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem orthogonal_reflection_identities (Q : QuadraticForm K V) {v : V} (hv : Q v ≠ 0) :
    (∀ x, reflect Q v x = x - (polar Q x v * (Q v)⁻¹) • v) ∧
      reflect Q v ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      reflect Q v * reflect Q v = 1 ∧
      (∀ x, polar Q x v = 0 → reflect Q v x = x) ∧
      ∀ g : V ≃ₗ[K] V, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q →
        g * reflect Q v * g⁻¹ = reflect Q (g v) := by
  refine ⟨fun x => ?_, reflect_mem_orthogonalGroup Q v, reflect_mul_self Q v,
    fun x hx => reflect_apply_of_polar_eq_zero (by rw [polar_comm, hx]),
    fun g hg => reflect_conj hg v⟩
  rw [reflect_apply hv, polar_comm, div_eq_mul_inv]

theorem quadratic_hyperbolic_splitting [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) {e f : V} (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) :
    (∀ x : V, x - polar Q x f • e - polar Q x e • f ∈
      {w : V | polar Q w e = 0 ∧ polar Q w f = 0}) ∧
    (∀ x : V, x = polar Q x f • e + polar Q x e • f + (x - polar Q x f • e - polar Q x e • f)) ∧
    (∀ (x : V) (a b : K) (w : V), polar Q w e = 0 → polar Q w f = 0 →
      x = a • e + b • f + w →
        a = polar Q x f ∧ b = polar Q x e ∧ w = x - polar Q x f • e - polar Q x e • f) ∧
    (∀ (a b : K) (w : V), polar Q w e = 0 → polar Q w f = 0 →
      Q (a • e + b • f + w) = a * b + Q w) ∧
    ∀ w : V, polar Q w e = 0 → polar Q w f = 0 →
      (∀ w' : V, polar Q w' e = 0 → polar Q w' f = 0 → polar Q w w' = 0) → w = 0 := by
  let P : HypPair Q := ⟨e, f, he, hf, hef⟩
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  have hee : polar Q e e = 0 := polar_self_eq_zero he
  have hff : polar Q f f = 0 := polar_self_eq_zero hf
  have hperp : ∀ w : V, w ∈ P.perp ↔ polar Q w e = 0 ∧ polar Q w f = 0 := fun w => by
    rw [HypPair.mem_perp]
    change polar Q e w = 0 ∧ polar Q f w = 0 ↔ _
    rw [polar_comm Q e w, polar_comm Q f w]
  refine ⟨fun x => (hperp _).1 (P.proj_mem_perp x), fun x => P.eq_add_proj x,
    fun x a b w hwe hwf hx => ?_, fun a b w hwe hwf => ?_, fun w hwe hwf hw => ?_⟩
  · have hxf : polar Q x f = a := by
      rw [hx, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hef, hff,
        hwf]
      ring
    have hxe : polar Q x e = b := by
      rw [hx, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hee, hfe,
        hwe]
      ring
    refine ⟨hxf.symm, hxe.symm, ?_⟩
    rw [hxf, hxe, hx]
    abel
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, he, hf]
    simp only [polar_add_left, polar_smul_left_eq, polar_smul_right_eq]
    rw [polar_comm Q e w, polar_comm Q f w, hwe, hwf, hef]
    ring
  · exact P.polarNondegOn_perp hQ w ((hperp w).2 ⟨hwe, hwf⟩) fun y hy =>
      hw y ((hperp y).1 hy).1 ((hperp y).1 hy).2

end CFSG.LocalAnalysis.ComponentInitial
