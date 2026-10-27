module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsLift
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open QuadraticMap TauCeti.QuadraticMap

section Plane

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  {Q : QuadraticForm F W}

theorem neg_one_ne_one_units_of_two_ne_zero (h2 : (2 : F) ≠ 0) : (-1 : Fˣ) ≠ 1 := by
  intro h
  apply h2
  have := congrArg Units.val h
  simp only [Units.val_neg, Units.val_one] at this
  linear_combination -this

theorem exists_det_eq_neg_one_pow (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {g : W ≃ₗ[F] W} (hg : g ∈ orthogonalGroup Q) :
    ∃ l : List ↥(orthogonalGroup Q), (∀ r ∈ l, ∃ (v : W) (_ : Invertible (Q v)),
        reflectionOrthogonal Q v = r) ∧ l.length ≤ Module.finrank F W ∧
      (l.prod : W ≃ₗ[F] W) = g ∧ LinearEquiv.det g = (-1 : Fˣ) ^ l.length := by
  have : NeZero (2 : F) := ⟨h2⟩
  have : Invertible (2 : F) := invertibleOfNonzero h2
  obtain ⟨l, hl, hlen, hprod⟩ := exists_reflectionOrthogonal_list_prod_eq Q
    (QuadraticMap.nondegenerate_polar_iff.mp hQ) ⟨g, hg⟩
  have hg' : (l.prod : W ≃ₗ[F] W) = g := congrArg Subtype.val hprod
  refine ⟨l, hl, hlen, hg', ?_⟩
  rw [← hg']
  exact det_list_prod_of_reflectionOrthogonal Q l hl

theorem det_eq_one_of_odd_orderOf (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {g : W ≃ₗ[F] W} (hg : g ∈ orthogonalGroup Q) (hodd : Odd (orderOf g)) :
    LinearEquiv.det g = 1 := by
  obtain ⟨l, -, -, -, hdet⟩ := exists_det_eq_neg_one_pow h2 hQ hg
  have hpow : LinearEquiv.det g ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Nat.even_or_odd l.length with he | ho
  · rw [hdet, he.neg_one_pow]
  · exfalso
    have h1 : LinearEquiv.det g = -1 := by rw [hdet, ho.neg_one_pow]
    rw [h1, hodd.neg_one_pow] at hpow
    exact neg_one_ne_one_units_of_two_ne_zero h2 hpow

omit [FiniteDimensional F W] in
theorem exists_quadratic_ne_zero [Nontrivial W] (hQ : (polarBilin Q).Nondegenerate) :
    ∃ v, Q v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  apply hx
  refine hQ.1 x fun y => ?_
  rw [polarBilin_apply_apply, polar, hcon, hcon, hcon]
  ring

theorem mul_self_eq_one_of_det_eq_neg_one (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F W ≤ 2) {g : W ≃ₗ[F] W} (hg : g ∈ orthogonalGroup Q)
    (hdet : LinearEquiv.det g = -1) : g * g = 1 := by
  obtain ⟨l, hl, hlen, hprod, hd⟩ := exists_det_eq_neg_one_pow h2 hQ hg
  rw [hdet] at hd
  have hlen3 : l.length = 0 ∨ l.length = 1 ∨ l.length = 2 := by omega
  rcases hlen3 with h0 | h1 | h2'
  · rw [h0, pow_zero] at hd
    exact absurd hd (neg_one_ne_one_units_of_two_ne_zero h2)
  · obtain ⟨r, rfl⟩ := List.length_eq_one_iff.mp h1
    obtain ⟨v, hv, hrv⟩ := hl r (by simp)
    have hrr : (r * r : ↥(orthogonalGroup Q)) = 1 := by
      rw [← hrv]
      exact reflectionOrthogonal_mul_self Q v
    rw [List.prod_singleton] at hprod
    rw [← hprod]
    exact congrArg Subtype.val hrr
  · rw [h2', neg_one_sq] at hd
    exact absurd hd (neg_one_ne_one_units_of_two_ne_zero h2)

theorem commute_of_det_eq_one_of_finrank_le_two (h2 : (2 : F) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank F W ≤ 2) {g h : W ≃ₗ[F] W}
    (hg : g ∈ orthogonalGroup Q) (hh : h ∈ orthogonalGroup Q) (hdg : LinearEquiv.det g = 1)
    (hdh : LinearEquiv.det h = 1) : g * h = h * g := by
  by_cases hW : Subsingleton W
  · exact LinearEquiv.ext fun x => Subsingleton.elim _ _
  · have : Nontrivial W := not_subsingleton_iff_nontrivial.mp hW
    obtain ⟨v, hv⟩ := exists_quadratic_ne_zero hQ
    have : Invertible (Q v) := invertibleOfNonzero hv
    set r : W ≃ₗ[F] W := (reflectionOrthogonal Q v : W ≃ₗ[F] W) with hr
    have hrO : r ∈ orthogonalGroup Q := (reflectionOrthogonal Q v).2
    have hrr : r * r = 1 := congrArg Subtype.val (reflectionOrthogonal_mul_self Q v)
    have hdr : LinearEquiv.det r = -1 := by rw [hr, coe_reflectionOrthogonal, det_reflection]
    have key : ∀ x : W ≃ₗ[F] W, x ∈ orthogonalGroup Q → LinearEquiv.det x = 1 →
        r * x * r = x⁻¹ := by
      intro x hx hdx
      have hxr : x * r ∈ orthogonalGroup Q := (orthogonalGroup Q).mul_mem hx hrO
      have hd : LinearEquiv.det (x * r) = -1 := by rw [map_mul, hdx, hdr, one_mul]
      have h1 := mul_self_eq_one_of_det_eq_neg_one h2 hQ hdim hxr hd
      have h3 : x * (r * x * r) = 1 := by
        calc x * (r * x * r) = (x * r) * (x * r) := by group
          _ = 1 := h1
      exact eq_inv_of_mul_eq_one_right h3
    have hgh : g * h ∈ orthogonalGroup Q := (orthogonalGroup Q).mul_mem hg hh
    have e1 := key g hg hdg
    have e2 := key h hh hdh
    have e3 := key (g * h) hgh (by rw [map_mul, hdg, hdh, one_mul])
    have e4 : r * (g * h) * r = (r * g * r) * (r * h * r) := by
      have : (r * g * r) * (r * h * r) = r * g * (r * r) * h * r := by group
      rw [this, hrr, mul_one]
      group
    rw [e4, e1, e2, mul_inv_rev] at e3
    calc g * h = (h⁻¹ * g⁻¹)⁻¹ := by group
      _ = (g⁻¹ * h⁻¹)⁻¹ := by rw [e3]
      _ = h * g := by group

theorem commute_map_of_isOddGenerated (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F W ≤ 2) {H : Type*} [Group H] (ρ : H →* (W ≃ₗ[F] W))
    (hρ : ∀ x, ρ x ∈ orthogonalGroup Q) {N : Subgroup H} (hN : IsOddGenerated N) :
    ∀ x ∈ N, ∀ y ∈ N, ρ x * ρ y = ρ y * ρ x := by
  set T : Set H := {x : H | x ∈ N ∧ Odd (orderOf x)} with hT
  have hdet : ∀ s ∈ T, LinearEquiv.det (ρ s) = 1 := fun s hs =>
    det_eq_one_of_odd_orderOf h2 hQ (hρ s) (hs.2.of_dvd_nat (orderOf_map_dvd ρ s))
  have hTc : ∀ s ∈ T, ∀ t ∈ T, ρ s * ρ t = ρ t * ρ s := fun s hs t ht =>
    commute_of_det_eq_one_of_finrank_le_two h2 hQ hdim (hρ s) (hρ t) (hdet s hs) (hdet t ht)
  have h1 : ∀ s ∈ T, ∀ x ∈ Subgroup.closure T, ρ x * ρ s = ρ s * ρ x := by
    intro s hs
    have hle : Subgroup.closure T ≤ (Subgroup.centralizer ({ρ s} : Set _)).comap ρ := by
      rw [Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact hTc t ht s hs
    intro x hx
    have := hle hx
    rwa [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at this
  have h2' : ∀ x ∈ Subgroup.closure T, ∀ y ∈ Subgroup.closure T, ρ y * ρ x = ρ x * ρ y := by
    intro x hx
    have hle : Subgroup.closure T ≤ (Subgroup.centralizer ({ρ x} : Set _)).comap ρ := by
      rw [Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (h1 t ht x hx).symm
    intro y hy
    have := hle hy
    rwa [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at this
  intro x hx y hy
  exact h2' y (hN hy) x (hN hx)

end Plane

end CFSG.ClassicalInvolution.Q3
