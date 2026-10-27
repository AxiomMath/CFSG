module

import CFSG.ClassicalInvolution.Phan.PhanP20Common
public import CFSG.ClassicalInvolution.Phan.PhanP14Minus
public import CFSG.ClassicalInvolution.Phan.PhanQ2Act

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4

section Witt

variable {F : Type} [Field F]

@[expose] noncomputable def combEquiv (h2 : (2 : F) ≠ 0) (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    (F × F) ≃ₗ[F] planeA ε hε h4 :=
  LinearEquiv.ofBijective (combMap h2 ε hε h4) (combMap_bijective h2)

theorem combEquiv_apply (h2 : (2 : F) ≠ 0) (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) (c : F × F) :
    ((combEquiv h2 ε hε h4 c : planeA ε hε h4) : V8 F) =
      c.1 • vecA1 F + c.2 • jOp ε (vecA1 F) := combMap_apply h2 c

@[expose] noncomputable def pairEmb (h2 : (2 : F) ≠ 0) {ε : F} (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0)
    (u v : V8 F) (hu : Q8 u = 1) (hv : Q8 v = ε) (huv : B8 u v = 0) :
    ((quadPlus 4 F).restrict (planeA ε hε h4)) →qᵢ quadPlus 4 F where
  toLinearMap := (LinearMap.coprod (LinearMap.toSpanSingleton F _ u)
    (LinearMap.toSpanSingleton F _ v)) ∘ₗ (combEquiv h2 ε hε h4).symm.toLinearMap
  map_app' x := by
    obtain ⟨c, rfl⟩ := (combEquiv h2 ε hε h4).surjective x
    have e1 : ((LinearMap.coprod (LinearMap.toSpanSingleton F _ u)
        (LinearMap.toSpanSingleton F _ v)) ∘ₗ (combEquiv h2 ε hε h4).symm.toLinearMap)
        (combEquiv h2 ε hε h4 c) = c.1 • u + c.2 • v := by
      simp
    change quadPlus 4 F (((LinearMap.coprod (LinearMap.toSpanSingleton F _ u)
        (LinearMap.toSpanSingleton F _ v)) ∘ₗ (combEquiv h2 ε hε h4).symm.toLinearMap)
        (combEquiv h2 ε hε h4 c)) = _
    rw [e1]
    have h3 : (quadPlus 4 F).restrict (planeA ε hε h4) (combEquiv h2 ε hε h4 c) =
        quadPlus 4 F ((combEquiv h2 ε hε h4 c : planeA ε hε h4) : V8 F) := rfl
    rw [h3, combEquiv_apply, Q_comb_A]
    have := Q8_lin c.1 c.2 u v
    rw [hu, hv, huv] at this
    change Q8 (c.1 • u + c.2 • v) = _ 
    rw [this]
    ring

theorem exists_spin_pair [Finite F] (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F)) {ε : F}
    (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) {u v : V8 F} (hu : Q8 u = 1) (hv : Q8 v = ε)
    (huv : B8 u v = 0) :
    ∃ y : spinGroup (quadPlus 4 F), spinAction (quadPlus 4 F) y (vecA1 F) = u ∧
      spinAction (quadPlus 4 F) y (jOp ε (vecA1 F)) = v := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hA := restrict_planeA_nondegenerate h2 hε h4
  have hdim : 2 ≤ Module.finrank F (LinearMap.BilinForm.orthogonal (quadPlus 4 F).polarBilin
      (planeA ε hε h4)) := by
    rw [finrank_planeA_perp h2 hε h4]
    norm_num
  obtain ⟨y, hy⟩ := exists_spin_extend_incl hodd (nondegenerate_polarBilin_quadPlus 4 F) hA hdim
    (pairEmb h2 hε h4 u v hu hv huv) (isometry_injective_of_nondegenerate hA _)
  have e1 : combEquiv h2 ε hε h4 (1, 0) = ⟨vecA1 F, vecA1_mem_planeA ε hε h4⟩ := by
    refine Subtype.ext ?_
    rw [combEquiv_apply]
    simp
  have e2 : combEquiv h2 ε hε h4 (0, 1) =
      ⟨jOp ε (vecA1 F), jOp_mem_planeA h2 (vecA1_mem_planeA ε hε h4)⟩ := by
    refine Subtype.ext ?_
    rw [combEquiv_apply]
    simp
  refine ⟨y, ?_, ?_⟩
  · have := hy (combEquiv h2 ε hε h4 (1, 0))
    rw [e1] at this
    rw [show vecA1 F = ((⟨vecA1 F, vecA1_mem_planeA ε hε h4⟩ : planeA ε hε h4) : V8 F) from rfl,
      this]
    change ((LinearMap.coprod (LinearMap.toSpanSingleton F _ u)
      (LinearMap.toSpanSingleton F _ v)) ∘ₗ (combEquiv h2 ε hε h4).symm.toLinearMap) _ = u
    rw [← e1]
    simp
  · have := hy (combEquiv h2 ε hε h4 (0, 1))
    rw [e2] at this
    rw [show jOp ε (vecA1 F) = ((⟨jOp ε (vecA1 F), jOp_mem_planeA h2
      (vecA1_mem_planeA ε hε h4)⟩ : planeA ε hε h4) : V8 F) from rfl, this]
    change ((LinearMap.coprod (LinearMap.toSpanSingleton F _ u)
      (LinearMap.toSpanSingleton F _ v)) ∘ₗ (combEquiv h2 ε hε h4).symm.toLinearMap) _ = v
    rw [← e2]
    simp

theorem exists_smul_z0 [Finite F] (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F)) {ε : F}
    (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) (z : NPair ε) :
    ∃ g : spinGroup (quadPlus 4 F), g • z0 ε = z := by
  obtain ⟨g, h1, h2'⟩ := exists_spin_pair h2 hodd hε h4 z.hx z.hy z.hxy
  refine ⟨g, ?_⟩
  ext1
  · exact h1
  · exact h2'

end Witt

end CFSG.ClassicalInvolution.PhanQ
