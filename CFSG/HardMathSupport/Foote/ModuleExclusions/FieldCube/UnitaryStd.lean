module

public import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.FieldCubeStd

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (mem_zpowers_of_pow_three_eq_one)

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem exists_semilinear_of_cube_eq_one_u (hq : 2 < p ^ f) {α : MulAut (unitaryPSU h 3)}
    (h3 : α ^ 3 = 1) :
    ∃ (A : unitaryIsom3 h) (σ : K ≃+* K), α = psuConj h A * psuField h σ ∧ σ ^ 3 = 1 := by
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
  obtain ⟨B', hB'⟩ := exists_psuConj_mul_psuField_pow h A σ 3
  rw [hB'] at h3
  exact ⟨A, σ, rfl, (eq_one_of_psuConj_mul_psuField_eq_one B' (σ ^ 3) h3).1⟩

theorem fieldCubeU_standardForm (hq : 2 < p ^ f)
    (B : Subgroup (MulAut (unitaryPSU h 3))) (hB : IsElemAbelian 3 B)
    (hout : ¬ B ≤ (psuConj h).range) :
    ∃ (g : unitaryIsom3 h) (σ : K ≃+* K), orderOf σ = 3 ∧
      B.map (MulAut.conj (psuConj h g)).toMonoidHom =
        Subgroup.zpowers (psuField h σ) ⊔ (B.map (MulAut.conj (psuConj h g)).toMonoidHom ⊓
          (psuConj h).range) ∧
      B.map (MulAut.conj (psuConj h g)).toMonoidHom ⊓ (psuConj h).range ≤
        Subgroup.centralizer {psuField h σ} := by
  have : Finite K := h.finite
  obtain ⟨b₀, hb₀B, hb₀⟩ := Set.not_subset.1 hout
  have hb₀3 : b₀ ^ 3 = 1 := hB.2 b₀ hb₀B
  obtain ⟨σ, hord, H, hH⟩ := unitary_order_three_field_descent hq b₀ hb₀3 hb₀
  refine ⟨H⁻¹, σ, hord, ?_⟩
  set c : MulAut (unitaryPSU h 3) := psuConj h H⁻¹ with hc
  have hclin : c ∈ (psuConj h).range := ⟨H⁻¹, rfl⟩
  set B' : Subgroup (MulAut (unitaryPSU h 3)) := B.map (MulAut.conj c).toMonoidHom with hB'
  have hcomm : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    have := congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    show c * b * c⁻¹ * (c * b' * c⁻¹) = c * b' * c⁻¹ * (c * b * c⁻¹)
    have h1 : b * b' = b' * b := this
    calc c * b * c⁻¹ * (c * b' * c⁻¹) = c * (b * b') * c⁻¹ := by group
      _ = c * (b' * b) * c⁻¹ := by rw [h1]
      _ = _ := by group
  have hf : psuField h σ ∈ B' := by
    refine ⟨b₀, hb₀B, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hH, hc, map_inv]
    group
  have hB'3 : ∀ x ∈ B', x ^ 3 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB.2 b hb, map_one]
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · intro x hx
    obtain ⟨A', τ, hx', hτ3⟩ := exists_semilinear_of_cube_eq_one_u hq (hB'3 x hx)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_pow_three_eq_one σ τ hord hτ3)
    have hfk : psuField h σ ^ k ∈ B' := Subgroup.zpow_mem B' hf k
    have hy : x * (psuField h σ ^ k)⁻¹ ∈ B' ⊓ (psuConj h).range := by
      refine ⟨B'.mul_mem hx (B'.inv_mem hfk), ?_⟩
      have : x * (psuField h σ ^ k)⁻¹ = psuConj h A' := by
        rw [hx', mul_assoc, ← map_zpow, hk, mul_inv_cancel, mul_one]
      rw [this]; exact ⟨A', rfl⟩
    have : x = psuField h σ ^ k * (x * (psuField h σ ^ k)⁻¹) := by
      rw [← mul_assoc, hcomm _ hfk x hx]
      group
    rw [this]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩) hy
  · exact sup_le (Subgroup.zpowers_le.2 hf) inf_le_left
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcomm _ hf x hx.1

end CFSG.HardMathSupport.Foote.ModuleExclusions
