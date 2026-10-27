module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearData

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

variable {X : Type*} [Group X] {J R D : Subgroup X} {q : ℕ}

namespace LinearSylowData

variable (hL : LinearSylowData J R D q)
include hL

theorem conj_torus_eq_mul {u : X} (huJ : u ∈ Subgroup.normalizer (J : Set X))
    (huR : u ∈ Subgroup.normalizer (R : Set X)) {x₀ y : X} (hx₀ : x₀ ∈ R) (hx₀1 : x₀ ≠ 1)
    (hy : y ∈ R) (hux₀ : u * x₀ = x₀ * u) (huy : u * y = y * u) {d : X} (hd : d ∈ D)
    (hdy : d * x₀ * d⁻¹ = y) : ∃ c ∈ R, u * d * u⁻¹ = c * d := by
  have hdJ : d ∈ J := hL.torus_le hd
  have hgJ : u * d * u⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp huJ d).mp hdJ
  have hgR : ∀ x ∈ R, u * d * u⁻¹ * x * (u * d * u⁻¹)⁻¹ ∈ R := by
    intro x hx
    have h1 : u⁻¹ * x * u ∈ R := (Subgroup.mem_normalizer_iff''.mp huR x).mp hx
    have h2 := hL.torus_conj d hd _ h1
    have h3 := (Subgroup.mem_normalizer_iff.mp huR _).mp h2
    convert h3 using 1
    group
  obtain ⟨c, hc, d', hd', hg⟩ := hL.normalizer _ hgJ hgR
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hx₀1
    calc x₀ = d⁻¹ * (d * x₀ * d⁻¹) * d := by group
      _ = 1 := by rw [hdy]; group
  have hux₀' : u⁻¹ * x₀ * u = x₀ := by
    rw [mul_assoc, ← hux₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have hd'y : d' * x₀ * d'⁻¹ = y := by
    have hd'eq : d' = c⁻¹ * (u * d * u⁻¹) := by rw [hg]; group
    have hgy : u * d * u⁻¹ * x₀ * (u * d * u⁻¹)⁻¹ = y := by
      calc u * d * u⁻¹ * x₀ * (u * d * u⁻¹)⁻¹ = u * (d * (u⁻¹ * x₀ * u) * d⁻¹) * u⁻¹ := by
            group
        _ = u * y * u⁻¹ := by rw [hux₀', hdy]
        _ = y := by rw [huy, mul_inv_cancel_right]
    rw [hd'eq]
    calc c⁻¹ * (u * d * u⁻¹) * x₀ * (c⁻¹ * (u * d * u⁻¹))⁻¹
        = c⁻¹ * (u * d * u⁻¹ * x₀ * (u * d * u⁻¹)⁻¹) * c := by group
      _ = c⁻¹ * y * c := by rw [hgy]
      _ = y := by rw [mul_assoc, hL.comm y hy c hc, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨d₀, -, huniq⟩ := hL.regular x₀ hx₀ hx₀1 y hy hy1
  have hdd' : d = d' := (huniq d ⟨hd, hdy⟩).trans (huniq d' ⟨hd', hd'y⟩).symm
  exact ⟨c, hc, hdd' ▸ hg⟩

theorem exists_mul_conj_eq {u : X} (huJ : u ∈ Subgroup.normalizer (J : Set X))
    (huR : u ∈ Subgroup.normalizer (R : Set X)) (hu2 : ∀ x ∈ R, u * u * x = x * (u * u))
    (hu : ∃ x ∈ R, u * x ≠ x * u) {c : X} (hc : c ∈ R) (hcu : u * c = c * u) :
    ∃ x ∈ R, x * (u * x * u⁻¹) = c := by
  have hconjR : ∀ x ∈ R, u * x * u⁻¹ ∈ R := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp huR x).mp hx
  obtain ⟨x₁, hx₁, hux₁⟩ := hu
  set y₀ := x₁ * (u * x₁ * u⁻¹) with hy₀
  have hy₀R : y₀ ∈ R := R.mul_mem hx₁ (hconjR x₁ hx₁)
  have hy₀1 : y₀ ≠ 1 := by
    intro h
    apply hux₁
    have h1 : u * x₁ * u⁻¹ = x₁ := by
      calc u * x₁ * u⁻¹ = x₁ * (x₁ * (u * x₁ * u⁻¹)) := by
            rw [← mul_assoc, hL.sq x₁ hx₁, one_mul]
        _ = x₁ := by rw [← hy₀, h, mul_one]
    calc u * x₁ = u * x₁ * u⁻¹ * u := by group
      _ = x₁ * u := by rw [h1]
  have huy₀ : u * y₀ = y₀ * u := by
    have h2 : u * (u * x₁ * u⁻¹) * u⁻¹ = x₁ := by
      calc u * (u * x₁ * u⁻¹) * u⁻¹ = u * u * x₁ * (u * u)⁻¹ := by group
        _ = x₁ := by rw [hu2 x₁ hx₁, mul_inv_cancel_right]
    have h3 : u * y₀ * u⁻¹ = y₀ := by
      calc u * y₀ * u⁻¹ = (u * x₁ * u⁻¹) * (u * (u * x₁ * u⁻¹) * u⁻¹) := by rw [hy₀]; group
        _ = (u * x₁ * u⁻¹) * x₁ := by rw [h2]
        _ = y₀ := by rw [hy₀, hL.comm _ (hconjR x₁ hx₁) x₁ hx₁]
    calc u * y₀ = u * y₀ * u⁻¹ * u := by group
      _ = y₀ * u := by rw [h3]
  by_cases hc1 : c = 1
  · exact ⟨1, R.one_mem, by rw [hc1]; group⟩
  obtain ⟨d, ⟨hd, hdc⟩, -⟩ := hL.regular y₀ hy₀R hy₀1 c hc hc1
  obtain ⟨c', hc', hud⟩ := hL.conj_torus_eq_mul huJ huR hy₀R hy₀1 hc huy₀ hcu hd hdc
  set x := d * x₁ * d⁻¹ with hx
  have hxR : x ∈ R := hL.torus_conj d hd x₁ hx₁
  have hux : u * x * u⁻¹ = d * (u * x₁ * u⁻¹) * d⁻¹ := by
    have hdu : u * d = c' * d * u := by
      calc u * d = u * d * u⁻¹ * u := by group
        _ = c' * d * u := by rw [hud]
    have hdR : d * (u * x₁ * u⁻¹) * d⁻¹ ∈ R := hL.torus_conj d hd _ (hconjR x₁ hx₁)
    calc u * x * u⁻¹ = (u * d) * x₁ * (u * d)⁻¹ := by rw [hx]; group
      _ = (c' * d * u) * x₁ * (c' * d * u)⁻¹ := by rw [hdu]
      _ = c' * (d * (u * x₁ * u⁻¹) * d⁻¹) * c'⁻¹ := by group
      _ = d * (u * x₁ * u⁻¹) * d⁻¹ := by
        rw [hL.comm c' hc' _ hdR, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨x, hxR, ?_⟩
  rw [hux, hx, ← hdc, hy₀]
  group

end LinearSylowData

end CFSG.ProperTwoGeneratedCore.Lemma37
