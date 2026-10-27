module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

variable {F : Type*} [Field F] [Finite F]

theorem exists_eq_pow_of_ringEquiv {p : ℕ} [Fact p.Prime] [CharP F p] (σ : F ≃+* F) :
    ∃ i : ℕ, ∀ x : F, σ x = x ^ (p ^ i) := by
  classical
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Fintype F := Fintype.ofFinite F
  let σAlg : F ≃ₐ[ZMod p] F := AlgEquiv.ofRingEquiv (f := σ) (by
    intro x
    have h : (σ.toRingHom.comp (algebraMap (ZMod p) F) : ZMod p →+* F) =
        algebraMap (ZMod p) F := RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x)
  obtain ⟨⟨i, _hi⟩, hσ⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 σAlg
  refine ⟨i, fun x => ?_⟩
  have hσx := DFunLike.congr_fun hσ x
  calc σ x = σAlg x := rfl
    _ = (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F ^ i) x := hσx.symm
    _ = ((⇑(FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F))^[i]) x := by
      rw [AlgEquiv.coe_pow]
    _ = x ^ (Fintype.card (ZMod p) ^ i) :=
      congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate (ZMod p) F i) x
    _ = x ^ (p ^ i) := by rw [ZMod.card]

theorem map_eq_self_of_sq_eq_one {G : Type*} [Field G] (σ : G ≃+* G) {u : G} (hu : u ^ 2 = 1) :
    σ u = u := by
  rcases sq_eq_one_iff.mp hu with h | h <;> simp [h]


theorem twist_ratio_eq_one {p : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2) {ν ρ π : F}
    (hν : ν ≠ 0) (σ τ : F ≃+* F) (hρ : ρ ^ 2 * σ ν = ν) (hπ : π ^ 2 * τ ν = ν) :
    τ ρ * π = ρ * σ π := by
  obtain ⟨i, hi⟩ := exists_eq_pow_of_ringEquiv (p := p) σ
  obtain ⟨j, hj⟩ := exists_eq_pow_of_ringEquiv (p := p) τ
  have hpo : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨a, ha⟩ := hpo.pow (n := i)
  obtain ⟨b, hb⟩ := hpo.pow (n := j)
  have hσν : σ ν = ν * (ν ^ a) ^ 2 := by rw [hi, ha]; ring
  have hτν : τ ν = ν * (ν ^ b) ^ 2 := by rw [hj, hb]; ring
  have hu : (ρ * ν ^ a) ^ 2 = 1 := by
    refine mul_left_cancel₀ hν ?_
    calc ν * (ρ * ν ^ a) ^ 2 = ρ ^ 2 * σ ν := by rw [hσν]; ring
      _ = ν * 1 := by rw [hρ, mul_one]
  have hv : (π * ν ^ b) ^ 2 = 1 := by
    refine mul_left_cancel₀ hν ?_
    calc ν * (π * ν ^ b) ^ 2 = π ^ 2 * τ ν := by rw [hτν]; ring
      _ = ν * 1 := by rw [hπ, mul_one]
  have hτu : τ ρ * τ ν ^ a = ρ * ν ^ a := by
    rw [← map_pow, ← map_mul]; exact map_eq_self_of_sq_eq_one τ hu
  have hσv : σ π * σ ν ^ b = π * ν ^ b := by
    rw [← map_pow, ← map_mul]; exact map_eq_self_of_sq_eq_one σ hv
  have hN : ν ^ (a * (2 * b + 1) + b) ≠ 0 := pow_ne_zero _ hν
  refine mul_right_cancel₀ hN ?_
  have e1 : τ ν ^ a = ν ^ (a * (2 * b + 1)) := by rw [hj, hb, ← pow_mul, mul_comm]
  have e2 : σ ν ^ b = ν ^ (b * (2 * a + 1)) := by rw [hi, ha, ← pow_mul, mul_comm]
  calc τ ρ * π * ν ^ (a * (2 * b + 1) + b) = (τ ρ * τ ν ^ a) * (π * ν ^ b) := by
        rw [e1, pow_add]; ring
    _ = (ρ * ν ^ a) * (σ π * σ ν ^ b) := by rw [hτu, hσv]
    _ = ρ * σ π * ν ^ (a * (2 * b + 1) + b) := by
        rw [e2, show a * (2 * b + 1) + b = a + b * (2 * a + 1) by ring, pow_add]; ring

theorem block_ratio_eq {p : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2) {ν l₀ l₁ k₀ k₁ : F}
    (hν : ν ≠ 0) (hl₀ : l₀ ≠ 0) (hk₀ : k₀ ≠ 0) (σ τ : F ≃+* F)
    (hl : l₁ ^ 2 * σ ν = l₀ ^ 2 * ν) (hk : k₁ ^ 2 * τ ν = k₀ ^ 2 * ν) :
    l₀ * σ k₀ * (τ l₁ * k₁) = l₁ * σ k₁ * (τ l₀ * k₀) := by
  have hρ : (l₁ / l₀) ^ 2 * σ ν = ν := by
    field_simp
    linear_combination hl
  have hπ : (k₁ / k₀) ^ 2 * τ ν = ν := by
    field_simp
    linear_combination hk
  have h := twist_ratio_eq_one hp hν σ τ hρ hπ
  have hτl₀ : τ l₀ ≠ 0 := (map_ne_zero τ).mpr hl₀
  have hσk₀ : σ k₀ ≠ 0 := (map_ne_zero σ).mpr hk₀
  rw [map_div₀, map_div₀] at h
  field_simp at h
  linear_combination h

end CFSG.ClassicalInvolution.Asc77.C5O
