module

public import CFSG.ClassicalGroups.Alternating.PointRadicalNormalizer
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.ClassicalGroups.Alternating

open CFSG.LocalAnalysis.ComponentInitial
open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

theorem mem_Lsp_iff_flag (hB : B.IsAlt) (hBn : B.Nondegenerate) {u : V} (hu : u ≠ 0)
    (g : Gsp B) :
    g ∈ Lsp B hB u ↔ g.app u = u ∧ (∀ x, B x u = 0 → ∃ c : K, g.app x - x = c • u) ∧
      ∀ x, B (g.app x - x) u = 0 := by
  constructor
  · intro hg
    obtain ⟨w, c, hw, hgs⟩ := mem_Lsp.mp hg
    obtain ⟨h1, h2⟩ := mem_pointRadical_props hB (mem_Lsp.mp hg)
    refine ⟨?_, h2, h1⟩
    have hsu : ((siegel B hB u w c : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u =
        ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u := by rw [hgs]
    rw [siegel_apply hB hw] at hsu
    show ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u = u
    rw [← hsu]
    simp [hB.self_eq_zero, hw]
  · rintro ⟨hgu, hflag, hperp⟩
    obtain ⟨x₀', hx₀'⟩ : ∃ x, B x u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (hBn.2 u hcon)
    set x₀ : V := (B x₀' u)⁻¹ • x₀' with hx₀
    have hx₀u : B x₀ u = 1 := by
      rw [hx₀, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hx₀']
    set w₀ : V := g.app x₀ - x₀ with hw₀
    have hw₀u : B w₀ u = 0 := hperp x₀
    have huw₀ : B u w₀ = 0 := by rw [← hB.neg_eq, hw₀u, neg_zero]
    set c : K := -B x₀ w₀ with hc
    have hgx₀ : g.app x₀ = x₀ + w₀ := by rw [hw₀]; abel
    have hux₀ : B u x₀ = -1 := by rw [← hB.neg_eq, hx₀u]
    have key : ∀ y : V, g.app y = y + B y u • w₀ + B y w₀ • u + (c * B y u) • u := by
      intro y
      set β : K := B y u with hβ
      set y' : V := y - β • x₀ with hy'
      have hy'u : B y' u = 0 := by
        rw [hy', map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
          hx₀u, mul_one, sub_self]
      obtain ⟨c', hc'⟩ := hflag y' hy'u
      have hy : y = β • x₀ + y' := by rw [hy']; abel
      have hgy' : g.app y' = y' + c' • u := by rw [← hc']; abel
      have hiso := Gsp.form_app g y' x₀
      rw [hgy', hgx₀] at hiso
      have hc'val : c' = B y' w₀ := by
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, hux₀, huw₀] at hiso
        linear_combination -hiso
      have hBy : B y w₀ = β * B x₀ w₀ + B y' w₀ := by
        conv_lhs => rw [hy]
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      have hx₀w : B x₀ w₀ = -c := by rw [hc, neg_neg]
      have hLHS : g.app y = β • (x₀ + w₀) + (y' + c' • u) := by
        conv_lhs => rw [hy]
        rw [Gsp.map_add, Gsp.map_smul, hgx₀, hgy']
      rw [hLHS, hBy, hx₀w, ← hc'val]
      conv_rhs => rw [hy]
      module
    have huw : B u w₀ = 0 := huw₀
    refine mem_Lsp.mpr ⟨w₀, c, huw, ?_⟩
    refine Units.ext (LinearMap.ext fun y => ?_)
    rw [siegel_apply hB huw c y]
    exact (key y).symm

end CFSG.ClassicalGroups.Alternating

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open CFSG.ClassicalGroups.Alternating
open Matrix

theorem mem_LspGL_iff_flag {m : ℕ} {K : Type} [Field K] {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    {A : GL (Fin m ⊕ Fin m) K} :
    A ∈ LspGL m K u ↔ A ∈ StatedSp m K ∧
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u ∧
      (∀ x, spForm m K x u = 0 → ∃ c : K,
        (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x - x = c • u) ∧
      ∀ x, spForm m K ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x - x) u = 0 := by
  rw [mem_LspGL_iff]
  constructor
  · rintro ⟨hA, h⟩
    have := (mem_Lsp_iff_flag spForm_isAlt spForm_nondegenerate hu _).mp h
    simp only [spEquiv_app] at this
    exact ⟨hA, this⟩
  · rintro ⟨hA, h⟩
    refine ⟨hA, (mem_Lsp_iff_flag spForm_isAlt spForm_nondegenerate hu _).mpr ?_⟩
    simpa only [spEquiv_app] using h

end CFSG.ClassicalGroups.Symplectic
