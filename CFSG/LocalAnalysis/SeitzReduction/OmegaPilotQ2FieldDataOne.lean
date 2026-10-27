module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataChart

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)

section Normalized

variable {G : Type} [Group G] {F : Type} [Field F] {r : ℕ} {τ : (Fin (r + 1) → Fˣ) →* G}
  {k : Fin (r + 1)}

theorem equivariant_of_normalized_q2
    (π : q2NbrCore τ k ≃* StatedOmega (StatedQuadPlus (r + 1) F))
    (hD : ∀ t : Fin (r + 1) → Fˣ, t k = 1 → τ t ∈ q2NbrCore τ k)
    (hnorm : ∀ (t : Fin (r + 1) → Fˣ) (ht : t k = 1),
      ((π ⟨τ t, hD t ht⟩ : StatedOmega (StatedQuadPlus (r + 1) F)) :
        GL (Fin (r + 1) ⊕ Fin (r + 1)) F) = minusNeighbourDiag (RingHom.id F) k t)
    (t : Fin (r + 1) → Fˣ) (hN : τ t ∈ normalizer (q2NbrCore τ k : Set G))
    (x : q2NbrCore τ k) :
    π ((q2NbrCore τ k).normalizerMonoidHom ⟨_, hN⟩ x) =
      (StatedOmega (StatedQuadPlus (r + 1) F)).normalizerMonoidHom
        ⟨minusNeighbourDiag (RingHom.id F) k t, minusNeighbourDiag_mem_normalizer _ k t⟩
          (π x) := by
  set c' : Fin (r + 1) → Fˣ := Pi.mulSingle k (t k) with hc'
  set t' : Fin (r + 1) → Fˣ := t * c'⁻¹ with ht'
  have ht'k : t' k = 1 := mul_mulSingle_inv_apply_self k t
  have htt : t = t' * c' := by rw [ht', inv_mul_cancel_right]
  have hgt : τ t = τ t' * τ c' := by rw [← map_mul, ← htt]
  have hgcX : τ c' ∈ (rootParam k).map τ := ⟨c', mulSingle_mem_rootParam k (t k), rfl⟩
  have hcomm : ∀ y : q2NbrCore τ k, (y : G) * τ c' = τ c' * y := fun y =>
    (mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ y.2) _ hgcX).symm
  have hval := hnorm t' ht'k
  rw [minusNeighbourDiag_mul_mulSingle_inv] at hval
  set y : q2NbrCore τ k := ⟨τ t', hD t' ht'k⟩
  have hconj : (q2NbrCore τ k).normalizerMonoidHom ⟨_, hN⟩ x = y * x * y⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change τ t * x * (τ t)⁻¹ = τ t' * x * (τ t')⁻¹
    rw [hgt, _root_.mul_inv_rev]
    calc τ t' * τ c' * ↑x * ((τ c')⁻¹ * (τ t')⁻¹) = τ t' * (τ c' * ↑x) * (τ c')⁻¹ * (τ t')⁻¹ := by
          group
      _ = τ t' * (↑x * τ c') * (τ c')⁻¹ * (τ t')⁻¹ := by rw [hcomm x]
      _ = τ t' * ↑x * (τ t')⁻¹ := by group
  rw [hconj, map_mul, map_mul, map_inv]
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hval]

@[expose] noncomputable def Q2FrameChart.ofNormalized
    (π : q2NbrCore τ k ≃* StatedOmega (StatedQuadPlus (r + 1) F))
    (hD : ∀ t : Fin (r + 1) → Fˣ, t k = 1 → τ t ∈ q2NbrCore τ k)
    (hnorm : ∀ (t : Fin (r + 1) → Fˣ) (ht : t k = 1),
      ((π ⟨τ t, hD t ht⟩ : StatedOmega (StatedQuadPlus (r + 1) F)) :
        GL (Fin (r + 1) ⊕ Fin (r + 1)) F) = minusNeighbourDiag (RingHom.id F) k t) :
    Q2FrameChart τ k where
  π := π
  equivariant t hN x := equivariant_of_normalized_q2 π hD hnorm t hN x

end Normalized

section Conj

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {r : ℕ}
  {τ : (Fin (r + 1) → Fˣ) →* G}

theorem mulSingle_zero_comp_cycleRange (k : Fin (r + 1)) (a : Fˣ) :
    (Pi.mulSingle (0 : Fin (r + 1)) a : Fin (r + 1) → Fˣ) ∘ Fin.cycleRange k =
      Pi.mulSingle k a := by
  funext i
  by_cases hi : i = k
  · subst hi
    simp [Fin.cycleRange_self]
  · have hne : Fin.cycleRange k i ≠ 0 := by
      intro h
      apply hi
      rw [← Fin.cycleRange_symm_zero k, ← h, Equiv.symm_apply_apply]
    simp [Function.comp_apply, Pi.mulSingle_eq_of_ne hne, Pi.mulSingle_eq_of_ne hi]

theorem map_conj_rootParam_zero {k : Fin (r + 1)} {w : G}
    (hw : ∀ s, w * τ s * w⁻¹ = τ (s ∘ Fin.cycleRange k)) :
    ((rootParam (0 : Fin (r + 1))).map τ).map (MulAut.conj w).toMonoidHom =
      (rootParam k).map τ := by
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, rfl⟩
    refine ⟨Pi.mulSingle k a, ⟨a, rfl⟩, ?_⟩
    change τ (Pi.mulSingle k a) = w * τ (Pi.mulSingle 0 a) * w⁻¹
    rw [hw, mulSingle_zero_comp_cycleRange]
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨τ (Pi.mulSingle 0 a), ⟨Pi.mulSingle 0 a, ⟨a, rfl⟩, rfl⟩, ?_⟩
    change w * τ (Pi.mulSingle 0 a) * w⁻¹ = τ (Pi.mulSingle k a)
    rw [hw, mulSingle_zero_comp_cycleRange]

theorem minusNeighbourDiag_zero_comp_cycleRange_symm (k : Fin (r + 1)) (t : Fin (r + 1) → Fˣ) :
    minusNeighbourDiag (RingHom.id F) 0 (t ∘ (Fin.cycleRange k).symm) =
      minusNeighbourDiag (RingHom.id F) k t := by
  rw [minusNeighbourDiag_apply, minusNeighbourDiag_apply]
  congr 3
  funext i
  rw [restrictParam_apply, restrictParam_apply, Function.comp_apply, Fin.succAbove_zero,
    Fin.cycleRange_symm_succ]

end Conj

end CFSG.SeitzReduction.OmegaPilot
