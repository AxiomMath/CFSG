module

public import CFSG.ClassicalInvolution.Asc77.AscSix66Aux

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C5O7Eng

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {K R R' : Subgroup G} {z u₁ u₂ a : G}

theorem comm_of_isUniqueInvolution_gen {J : Subgroup G} {w x : G} (hw : IsUniqueInvolution J w)
    (hx : x ∈ J) : x * w = w * x := by
  have h1 : x * w * x⁻¹ ∈ J := J.mul_mem (J.mul_mem hx hw.mem) (J.inv_mem hx)
  have h2 : (x * w * x⁻¹) * (x * w * x⁻¹) = 1 := by
    calc (x * w * x⁻¹) * (x * w * x⁻¹) = x * (w * w) * x⁻¹ := by group
      _ = 1 := by rw [hw.sq]; group
  rcases hw.unique _ h1 h2 with h | h
  · exfalso
    apply hw.ne_one
    calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  · calc x * w = (x * w * x⁻¹) * x := by group
      _ = w * x := by rw [h]

theorem not_conj_au_gen
    (hz : IsUniqueInvolution K z)
    (hz1 : z ≠ 1)
    (hRK : R ≤ K)
    (hu₁R : u₁ ∈ R)
    (hu₁o : orderOf u₁ = 4)
    (hu₂R' : u₂ ∈ R')
    (hcomm : Commutes R R')
    (hqR : IsQuatSub R)
    (haR : ∀ r ∈ R, a * r = r * a)
    (hsq4 : ∀ {u : G}, u ∈ K → orderOf u = 4 → u * u = z)
    (hnc : ∀ {y : G}, y * z * y⁻¹ ≠ z → ∀ {x : G}, x ∈ K → orderOf x = 4 →
      (y * z * y⁻¹) * x ≠
        x * (y * z * y⁻¹))
    (g : G) : g * z * g⁻¹ ≠ a * (u₁ * u₂) := by
  intro hg
  have hu₁K : u₁ ∈ K := hRK hu₁R
  have hu₁sq : u₁ * u₁ = z := hsq4 hu₁K hu₁o
  have hu12 : u₁ * u₂ = u₂ * u₁ := hcomm u₁ hu₁R u₂ hu₂R'
  have hne : g * z * g⁻¹ ≠ z := by
    rw [hg]
    intro h
    have hu₁c : ∀ r ∈ R, u₁ * r = r * u₁ := by
      intro r hr
      have hra : a * r = r * a := haR r hr
      have hrz : r * z = z * r := comm_of_isUniqueInvolution_gen hz (hRK hr)
      have hru₂ : r * u₂ = u₂ * r := hcomm r hr u₂ hu₂R'
      have e : u₁ = a⁻¹ * z * u₂⁻¹ := by
        calc u₁ = a⁻¹ * (a * (u₁ * u₂)) * u₂⁻¹ := by group
          _ = a⁻¹ * z * u₂⁻¹ := by rw [h]
      have hrai : r * a⁻¹ = a⁻¹ * r := by
        calc r * a⁻¹ = a⁻¹ * (a * r) * a⁻¹ := by group
          _ = a⁻¹ * (r * a) * a⁻¹ := by rw [hra]
          _ = a⁻¹ * r := by group
      have hru₂i : r * u₂⁻¹ = u₂⁻¹ * r := by
        calc r * u₂⁻¹ = u₂⁻¹ * (u₂ * r) * u₂⁻¹ := by group
          _ = u₂⁻¹ * (r * u₂) * u₂⁻¹ := by rw [hru₂]
          _ = u₂⁻¹ * r := by group
      rw [e]
      calc a⁻¹ * z * u₂⁻¹ * r = a⁻¹ * z * (r * u₂⁻¹) := by rw [mul_assoc, hru₂i]
        _ = a⁻¹ * (z * r) * u₂⁻¹ := by group
        _ = a⁻¹ * (r * z) * u₂⁻¹ := by rw [hrz]
        _ = (a⁻¹ * r) * z * u₂⁻¹ := by group
        _ = (r * a⁻¹) * z * u₂⁻¹ := by rw [hrai]
        _ = r * (a⁻¹ * z * u₂⁻¹) := by group
    have h2 := hqR.sq_eq_one_of_central hu₁R hu₁c
    rw [hu₁sq] at h2
    exact hz1 h2
  refine hnc hne hu₁K hu₁o ?_
  rw [hg]
  have hau : a * u₁ = u₁ * a := haR u₁ hu₁R
  calc a * (u₁ * u₂) * u₁ = a * u₁ * (u₂ * u₁) := by group
    _ = a * u₁ * (u₁ * u₂) := by rw [← hu12]
    _ = (a * u₁) * u₁ * u₂ := by group
    _ = (u₁ * a) * u₁ * u₂ := by rw [hau]
    _ = u₁ * (a * u₁) * u₂ := by group
    _ = u₁ * (u₁ * a) * u₂ := by rw [hau]
    _ = u₁ * (a * (u₁ * u₂)) := by rw [← hau]; group

end C5O7Eng

end CFSG.ClassicalInvolution.Asc77
