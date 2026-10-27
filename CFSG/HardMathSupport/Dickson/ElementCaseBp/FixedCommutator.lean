module

public import CFSG.HardMathSupport.Dickson.ElementCaseBp.InnerAut
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Dickson.ElementCaseBp

open scoped commutatorElement

private theorem exists_center_mul_of_commute_conj {Q : Type*} [Group Q] (φ : MulAut Q) (k : Q)
    (h : Commute (MulAut.conj k) φ) : ∃ z ∈ Subgroup.center Q, φ k = k * z := by
  obtain ⟨z, hz⟩ : ∃ z : Q, φ k = k * z := ⟨k⁻¹ * φ k, by group⟩
  refine ⟨z, ?_, hz⟩
  have h2 : φ * MulAut.conj k * φ⁻¹ = MulAut.conj k := by
    rw [← h.eq, mul_inv_cancel_right]
  have hc : MulAut.conj k = MulAut.conj (φ k) := h2.symm.trans (mul_conj_mul_inv φ k)
  rw [Subgroup.mem_center_iff]
  intro g
  have hg := DFunLike.congr_fun hc g
  rw [MulAut.conj_apply, MulAut.conj_apply, hz] at hg
  have e : g = z * g * z⁻¹ := by
    calc g = k⁻¹ * (k * g * k⁻¹) * k := by group
      _ = k⁻¹ * (k * z * g * (k * z)⁻¹) * k := by rw [hg]
      _ = z * g * z⁻¹ := by group
  calc g * z = z * g * z⁻¹ * z := by rw [← e]
    _ = z * g := by group

private theorem commutatorElement_central_mul_left {Q : Type*} [Group Q] {z : Q}
    (hz : z ∈ Subgroup.center Q) (g h : Q) : ⁅z * g, h⁆ = ⁅g, h⁆ := by
  have key : ∀ a : Q, z * a = a * z := fun a => (Subgroup.mem_center_iff.1 hz a).symm
  rw [commutatorElement_def, commutatorElement_def]
  simp only [mul_inv_rev]
  calc z * g * h * (g⁻¹ * z⁻¹) * h⁻¹ = z * (g * h * g⁻¹) * z⁻¹ * h⁻¹ := by group
    _ = (g * h * g⁻¹) * z * z⁻¹ * h⁻¹ := by rw [key]
    _ = g * h * g⁻¹ * h⁻¹ := by group

private theorem commutatorElement_central_mul_right {Q : Type*} [Group Q] {z : Q}
    (hz : z ∈ Subgroup.center Q) (g h : Q) : ⁅g, z * h⁆ = ⁅g, h⁆ := by
  have key : ∀ a : Q, z * a = a * z := fun a => (Subgroup.mem_center_iff.1 hz a).symm
  rw [commutatorElement_def, commutatorElement_def]
  simp only [mul_inv_rev]
  calc g * (z * h) * g⁻¹ * (h⁻¹ * z⁻¹) = (g * z) * h * g⁻¹ * h⁻¹ * z⁻¹ := by group
    _ = z * (g * h * g⁻¹ * h⁻¹) * z⁻¹ := by rw [← key g]; group
    _ = (g * h * g⁻¹ * h⁻¹) * z * z⁻¹ := by rw [key]
    _ = g * h * g⁻¹ * h⁻¹ := by group

private theorem commutatorElement_mul_mul_central {Q : Type*} [Group Q] {a b z₁ z₂ : Q}
    (hz₁ : z₁ ∈ Subgroup.center Q) (hz₂ : z₂ ∈ Subgroup.center Q) :
    ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  rw [Subgroup.mem_center_iff.1 hz₁ a, Subgroup.mem_center_iff.1 hz₂ b,
    commutatorElement_central_mul_left hz₁, commutatorElement_central_mul_right hz₂]

theorem commutatorElement_mem_centralizer_of_commute_conj {G : Type*} [Group G]
    {K : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) {k₁ k₂ : K}
    (h₁ : Commute (MulAut.conj k₁) (Subgroup.normalizerMonoidHom K ⟨x, hx⟩))
    (h₂ : Commute (MulAut.conj k₂) (Subgroup.normalizerMonoidHom K ⟨x, hx⟩)) :
    ((⁅k₁, k₂⁆ : K) : G) ∈ Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨z₁, hz₁, hφ₁⟩ :=
    exists_center_mul_of_commute_conj (Subgroup.normalizerMonoidHom K ⟨x, hx⟩) k₁ h₁
  obtain ⟨z₂, hz₂, hφ₂⟩ :=
    exists_center_mul_of_commute_conj (Subgroup.normalizerMonoidHom K ⟨x, hx⟩) k₂ h₂
  have hfix : (Subgroup.normalizerMonoidHom K ⟨x, hx⟩) ⁅k₁, k₂⁆ = ⁅k₁, k₂⁆ := by
    rw [map_commutatorElement, hφ₁, hφ₂]
    exact commutatorElement_mul_mul_central hz₁ hz₂
  have h3 : ((Subgroup.normalizerMonoidHom K ⟨x, hx⟩) ⁅k₁, k₂⁆ : G) =
      ((⁅k₁, k₂⁆ : K) : G) := by
    rw [hfix]
  rw [normalizerMonoidHom_apply_coe] at h3
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (mul_inv_eq_iff_eq_mul.1 h3).symm

end CFSG.HardMathSupport.Dickson.ElementCaseBp
