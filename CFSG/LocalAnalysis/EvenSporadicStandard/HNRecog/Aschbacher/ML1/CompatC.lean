module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.InnerAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Subgroup CFSG.RankThree.Literature.FSmith

variable {C C' : Type} [Group C] [Group C'] {Q : Subgroup C} {Q' : Subgroup C'}
  [hQn : Q.Normal] [hQn' : Q'.Normal]

private lemma mulEquiv_symm_mem_center {G H : Type*} [Group G] [Group H]
    (φ : G ≃* H) {c : H} (hc : c ∈ Subgroup.center H) :
    φ.symm c ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro x
  apply φ.injective
  simp only [map_mul, MulEquiv.apply_symm_apply]
  exact hc (φ x)

theorem exists_conj_compat [Finite Q'] (hE' : IsExtraspecialPGroup 2 Q') (φ₀ : ↥Q ≃* ↥Q')
    (l : C) (l' : C')
    (h : ∀ x : ↥Q, φ₀ (conjAut hQn l x) * (conjAut hQn' l' (φ₀ x))⁻¹ ∈ Subgroup.center ↥Q') :
    ∃ q : ↥Q', ∀ x : ↥Q, φ₀ (conjAut hQn l x) = conjAut hQn' ((q : C') * l') (φ₀ x) := by
  let ν : ↥Q' ≃* ↥Q' := conjAut hQn' l'
  let μ : ↥Q' ≃* ↥Q' := φ₀.symm.trans ((conjAut hQn l).trans φ₀)
  let γ : ↥Q' ≃* ↥Q' := ν.symm.trans μ
  have hγ : ∀ y : ↥Q', γ y * y⁻¹ ∈ Subgroup.center ↥Q' := by
    intro y
    have hx := h (φ₀.symm (ν.symm y))
    have hA : γ y = φ₀ (conjAut hQn l (φ₀.symm (ν.symm y))) := by
      simp [γ, μ, MulEquiv.trans_apply]
    have hB : conjAut hQn' l' (φ₀ (φ₀.symm (ν.symm y))) = y := by
      rw [MulEquiv.apply_symm_apply]
      exact MulEquiv.apply_symm_apply ν y
    have hEq : γ y * y⁻¹ = φ₀ (conjAut hQn l (φ₀.symm (ν.symm y))) *
        (conjAut hQn' l' (φ₀ (φ₀.symm (ν.symm y))))⁻¹ := by rw [hA, hB]
    rw [hEq]
    exact hx
  obtain ⟨q, hq⟩ := exists_conj_of_forall_mul_inv_mem_center hE' γ hγ
  refine ⟨q, fun x => ?_⟩
  have h1 : γ (ν (φ₀ x)) = q * ν (φ₀ x) * q⁻¹ := hq (ν (φ₀ x))
  have hγx : γ (ν (φ₀ x)) = φ₀ (conjAut hQn l x) := by
    simp [γ, μ, ν, MulEquiv.trans_apply]
  rw [← hγx, h1]
  apply Subtype.ext
  rw [conjAut_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ν, conjAut_apply]
  group

theorem exists_conj_compat' [Finite Q] (hE : IsExtraspecialPGroup 2 Q) (φ₀ : ↥Q ≃* ↥Q')
    (l : C) (l' : C')
    (h : ∀ x : ↥Q, φ₀ (conjAut hQn l x) * (conjAut hQn' l' (φ₀ x))⁻¹ ∈ Subgroup.center ↥Q') :
    ∃ q : ↥Q, ∀ x : ↥Q, φ₀ (conjAut hQn ((q : C) * l) x) = conjAut hQn' l' (φ₀ x) := by
  let μ₁ : ↥Q ≃* ↥Q := conjAut hQn l
  let ν₁ : ↥Q ≃* ↥Q := φ₀.trans ((conjAut hQn' l').trans φ₀.symm)
  let γ₁ : ↥Q ≃* ↥Q := μ₁.symm.trans ν₁
  have hmem : ∀ x : ↥Q, μ₁ x * (ν₁ x)⁻¹ ∈ Subgroup.center ↥Q := by
    intro x
    have hx := h x
    have hc : φ₀.symm (φ₀ (conjAut hQn l x) *
        (conjAut hQn' l' (φ₀ x))⁻¹) ∈ Subgroup.center ↥Q :=
      mulEquiv_symm_mem_center φ₀ hx
    simpa [μ₁, ν₁, MulEquiv.trans_apply] using hc
  have hγ₁ : ∀ y : ↥Q, γ₁ y * y⁻¹ ∈ Subgroup.center ↥Q := by
    intro y
    have h1 := hmem (μ₁.symm y)
    have h2 : (y * (γ₁ y)⁻¹) ∈ Subgroup.center ↥Q := by
      have h2' : y * (γ₁ y)⁻¹ = μ₁ (μ₁.symm y) * (ν₁ (μ₁.symm y))⁻¹ := by
        simp [γ₁, MulEquiv.trans_apply]
      rw [h2']
      exact h1
    have h3 : (y * (γ₁ y)⁻¹)⁻¹ ∈ Subgroup.center ↥Q := inv_mem h2
    simpa only [mul_inv_rev, inv_inv] using h3
  obtain ⟨q, hq⟩ := exists_conj_of_forall_mul_inv_mem_center hE γ₁ hγ₁
  refine ⟨q, fun x => ?_⟩
  have hν : γ₁ (μ₁ x) = ν₁ x := by simp [γ₁, MulEquiv.trans_apply]
  have h1 : ν₁ x = q * μ₁ x * q⁻¹ := by rw [← hν, hq (μ₁ x)]
  have hstep : φ₀ (conjAut hQn ((q : C) * l) x) = φ₀ (q * μ₁ x * q⁻¹) := by
    congr 1
    apply Subtype.ext
    rw [conjAut_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, μ₁, conjAut_apply]
    group
  rw [hstep, ← h1]
  simp [ν₁, MulEquiv.trans_apply]

end CFSG.EvenSporadicStandard.HNRecog.ML1
