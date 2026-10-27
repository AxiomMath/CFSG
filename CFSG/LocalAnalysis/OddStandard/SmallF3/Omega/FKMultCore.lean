module

public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply nondegenerate_polarBilin_quadPlus
  polar_quadPlus_single_inl)
open QuadraticMap

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

private abbrev fk_V : Type := Fin 4 ⊕ Fin 4 → GaloisField 3 1

theorem fk_mult_core
    (A g₂ g₃ : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin 4 ⊕ Fin 4 → GaloisField 3 1))
    (N₂ N₃ : Module.End (GaloisField 3 1) (Fin 4 ⊕ Fin 4 → GaloisField 3 1))
    (μ ε₂ ε₃ : GaloisField 3 1) (hμ : μ ≠ 0)
    (hA : ∀ v, quadPlus 4 (GaloisField 3 1) (A v) = μ * quadPlus 4 (GaloisField 3 1) v)
    (hg₂ : ∀ v, quadPlus 4 (GaloisField 3 1) (g₂ v) = quadPlus 4 (GaloisField 3 1) v)
    (hg₃ : ∀ v, quadPlus 4 (GaloisField 3 1) (g₃ v) = quadPlus 4 (GaloisField 3 1) v)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hε₃ : ε₃ = 1 ∨ ε₃ = -1)
    (hN : ∀ v, N₂ (N₃ v) =
      -(v (Sum.inr 2)) • (Pi.single (Sum.inl 2) 1 : Fin 4 ⊕ Fin 4 → GaloisField 3 1))
    (h₂ : ∀ v, A (N₂ (A.symm v)) = ε₂ • g₂ (N₂ (g₂.symm v)))
    (h₃ : ∀ v, A (N₃ (A.symm v)) = ε₃ • g₃ (N₃ (g₃.symm v)))
    (c₂₃ : ∀ v, g₂ (N₃ v) = N₃ (g₂ v)) (c₃₂ : ∀ v, g₃ (N₂ v) = N₂ (g₃ v))
    (c : ∀ v, g₂ (g₃ v) = g₃ (g₂ v)) :
    μ = ε₂ * ε₃ := by
  classical
  haveI : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  let e : fk_V := Pi.single (Sum.inl 2) 1
  set ε : GaloisField 3 1 := ε₂ * ε₃ with hε
  have he : e ≠ 0 := by
    intro h
    have h1 : (1 : GaloisField 3 1) = 0 := by
      have := congrFun h (Sum.inl 2)
      simpa [e] using this
    exact one_ne_zero h1
  have hp : A e ≠ 0 := by
    intro h
    apply he
    rw [← A.symm_apply_apply e, h, map_zero]
  have hq : g₂ (g₃ e) ≠ 0 := by
    intro h
    apply he
    have h1 : g₃ e = 0 := by
      apply g₂.injective
      rw [h, map_zero]
    apply g₃.injective
    rw [h1, map_zero]
  have hA_polar : ∀ v w : fk_V, polar Q₄ (A v) (A w) = μ * polar Q₄ v w := by
    intro v w
    have h1 : A (v + w) = A v + A w := A.map_add v w
    simp only [polar]
    rw [← h1, hA (v + w), hA v, hA w]
    ring
  have hg₂_polar : ∀ v w : fk_V, polar Q₄ (g₂ v) (g₂ w) = polar Q₄ v w := by
    intro v w
    have h1 : g₂ (v + w) = g₂ v + g₂ w := g₂.map_add v w
    simp only [polar]
    rw [← h1, hg₂ (v + w), hg₂ v, hg₂ w]
  have hg₃_polar : ∀ v w : fk_V, polar Q₄ (g₃ v) (g₃ w) = polar Q₄ v w := by
    intro v w
    have h1 : g₃ (v + w) = g₃ v + g₃ w := g₃.map_add v w
    simp only [polar]
    rw [← h1, hg₃ (v + w), hg₃ v, hg₃ w]
  have hA_symm : ∀ v w : fk_V,
      polar Q₄ (A.symm v) w = μ⁻¹ * polar Q₄ v (A w) := by
    intro v w
    have h := hA_polar (A.symm v) w
    rw [A.apply_symm_apply] at h
    rw [h, inv_mul_cancel_left₀ hμ]
  have hg₂_symm : ∀ v w : fk_V, polar Q₄ (g₂.symm v) w = polar Q₄ v (g₂ w) := by
    intro v w
    have h := hg₂_polar (g₂.symm v) w
    rw [g₂.apply_symm_apply] at h
    exact h.symm
  have hg₃_symm : ∀ v w : fk_V, polar Q₄ (g₃.symm v) w = polar Q₄ v (g₃ w) := by
    intro v w
    have h := hg₃_polar (g₃.symm v) w
    rw [g₃.apply_symm_apply] at h
    exact h.symm
  have hg₂_symm_g₃ : ∀ x : fk_V, g₂.symm (g₃ x) = g₃ (g₂.symm x) := by
    intro x
    apply g₂.injective
    rw [g₂.apply_symm_apply, c (g₂.symm x), g₂.apply_symm_apply]
  have hg₂_g₃_symm : ∀ x : fk_V, g₂ (g₃.symm x) = g₃.symm (g₂ x) := by
    intro x
    apply g₃.injective
    rw [g₃.apply_symm_apply, ← c (g₃.symm x), g₃.apply_symm_apply]
  have hg₂_symm_g₃_symm : ∀ x : fk_V, g₂.symm (g₃.symm x) = g₃.symm (g₂.symm x) := by
    intro x
    apply g₂.injective
    rw [g₂.apply_symm_apply, hg₂_g₃_symm, g₂.apply_symm_apply]
  have hN₃_g₂_symm : ∀ x : fk_V, N₃ (g₂.symm x) = g₂.symm (N₃ x) := by
    intro x
    have h : g₂ (N₃ (g₂.symm x)) = N₃ x := by rw [c₂₃, g₂.apply_symm_apply]
    rw [← h, g₂.symm_apply_apply]
  have hN₂_g₃ : ∀ x : fk_V, N₂ (g₃ x) = g₃ (N₂ x) := fun x => (c₃₂ x).symm
  have hconj : ∀ v : fk_V, A (N₂ (N₃ (A.symm v))) =
      ε • g₂ (g₃ (N₂ (N₃ (g₃.symm (g₂.symm v))))) := by
    intro v
    have h2 := h₂ (A (N₃ (A.symm v)))
    rw [A.symm_apply_apply] at h2
    have h3 := h₃ v
    rw [h2, h3]
    simp only [map_smul]
    rw [smul_smul, ← hε]
    congr 1
    congr 1
    rw [hg₂_symm_g₃, ← hN₃_g₂_symm, hg₂_symm_g₃_symm, hN₂_g₃]
  have hLHS : ∀ v : fk_V, A (N₂ (N₃ (A.symm v))) =
      -(μ⁻¹ * polar Q₄ v (A e)) • A e := by
    intro v
    have hscalar : A.symm v (Sum.inr 2) = μ⁻¹ * polar Q₄ v (A e) := by
      rw [← polar_quadPlus_single_inl 4 (GaloisField 3 1) (A.symm v) 2, hA_symm v e]
    rw [hN (A.symm v), map_smul, hscalar]
  have hRHS : ∀ v : fk_V,
      ε • g₂ (g₃ (N₂ (N₃ (g₃.symm (g₂.symm v))))) =
        -(ε * polar Q₄ v (g₂ (g₃ e))) • g₂ (g₃ e) := by
    intro v
    have hscalar : g₃.symm (g₂.symm v) (Sum.inr 2) = polar Q₄ v (g₂ (g₃ e)) := by
      rw [← polar_quadPlus_single_inl 4 (GaloisField 3 1) (g₃.symm (g₂.symm v)) 2,
        hg₃_symm (g₂.symm v) e, hg₂_symm v (g₃ e)]
    rw [hN (g₃.symm (g₂.symm v)), map_smul, map_smul, hscalar, smul_smul, mul_neg]
  have hrank : ∀ v : fk_V, (μ⁻¹ * polar Q₄ v (A e)) • A e =
      (ε * polar Q₄ v (g₂ (g₃ e))) • g₂ (g₃ e) := by
    intro v
    have h := hconj v
    rw [hLHS v, hRHS v] at h
    have h' := congrArg Neg.neg h
    simp only [neg_smul, neg_neg] at h'
    exact h'
  have hnd := nondegenerate_polarBilin_quadPlus 4 (GaloisField 3 1)
  obtain ⟨v₀, hv₀⟩ : ∃ v : fk_V, polar Q₄ v (A e) ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (hnd.2 (A e) fun v => by simpa using h v)
  let v₁ : fk_V := (polar Q₄ v₀ (A e))⁻¹ • v₀
  have hv₁ : polar Q₄ v₁ (A e) = 1 := by
    show polar Q₄ ((polar Q₄ v₀ (A e))⁻¹ • v₀) (A e) = 1
    rw [polar_smul_left, smul_eq_mul, inv_mul_cancel₀ hv₀]
  obtain ⟨w₀, hw₀⟩ : ∃ w : fk_V, polar Q₄ w (g₂ (g₃ e)) ≠ 0 := by
    by_contra h
    push Not at h
    exact hq (hnd.2 (g₂ (g₃ e)) fun v => by simpa using h v)
  let w₁ : fk_V := (polar Q₄ w₀ (g₂ (g₃ e)))⁻¹ • w₀
  have hw₁ : polar Q₄ w₁ (g₂ (g₃ e)) = 1 := by
    show polar Q₄ ((polar Q₄ w₀ (g₂ (g₃ e)))⁻¹ • w₀) (g₂ (g₃ e)) = 1
    rw [polar_smul_left, smul_eq_mul, inv_mul_cancel₀ hw₀]
  have h1 := hrank v₁
  rw [hv₁, mul_one] at h1
  have hpq : A e = (μ * (ε * polar Q₄ v₁ (g₂ (g₃ e)))) • g₂ (g₃ e) := by
    have := congrArg (fun x => μ • x) h1
    simpa [smul_smul, mul_inv_cancel₀ hμ] using this
  generalize hν : μ * (ε * polar Q₄ v₁ (g₂ (g₃ e))) = ν at hpq
  have hpq' : A e = ν • g₂ (g₃ e) := hpq
  have hνne : ν ≠ 0 := by
    intro h
    apply hp
    rw [hpq', h, zero_smul]
  have hcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card (p := 3) (n := 1) one_ne_zero, pow_one]
  have hcard' : Fintype.card (GaloisField 3 1) = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have hνsq : ν * ν = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one ν hνne
    rw [hcard'] at h
    norm_num at h
    rcases h with h | h <;> rw [h] <;> ring
  have h2 := hrank w₁
  rw [hw₁, mul_one] at h2
  have hw₁p : polar Q₄ w₁ (A e) = ν := by
    rw [hpq', polar_smul_right, smul_eq_mul, hw₁, mul_one]
  rw [hw₁p] at h2
  rw [hpq'] at h2
  rw [smul_smul] at h2
  have hcoef : μ⁻¹ * ν * ν = ε :=
    smul_left_injective (R := GaloisField 3 1) hq h2
  have hminv : μ⁻¹ = ε := by
    have := hcoef
    rw [mul_assoc, hνsq, mul_one] at this
    exact this
  have hεcases : ε = 1 ∨ ε = -1 := by
    rw [hε]
    rcases hε₂ with rfl | rfl <;> rcases hε₃ with rfl | rfl <;> simp
  have hεsq : ε * ε = 1 := by
    rcases hεcases with h | h <;> rw [h] <;> ring
  have hεne : ε ≠ 0 := by
    intro h
    have h' : (0 : GaloisField 3 1) = 1 := by simpa [h] using hεsq
    exact zero_ne_one h'
  have hεμ : ε * μ = 1 := by
    have h := congrArg (fun x => x * μ) hminv
    rw [h.symm, inv_mul_cancel₀ hμ]
  have hμeq : μ = ε := by
    have : ε * μ = ε * ε := by rw [hεμ, hεsq]
    exact mul_left_cancel₀ hεne this
  exact hμeq

end CFSG.OddStandard.SmallF3.Omega
