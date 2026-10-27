module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open CFSG.EvenSporadicStandard.HNRecog

@[expose] def In2A (t : ↥P1408) : Prop := IsConj pA t ∨ IsConj (pA * pZ) t ∨ IsConj pB t

@[expose] def In2B (t : ↥P1408) : Prop := IsConj pZ t ∨ IsConj pZ₁ t

theorem In2A.map_conj {w : ↥P1408} (h : In2A w) (x : ↥P1408) : In2A (x * w * x⁻¹) := by
  have hx : IsConj w (x * w * x⁻¹) := isConj_iff.2 ⟨x, rfl⟩
  exact h.imp (fun h => h.trans hx) fun h => h.imp (fun h => h.trans hx) fun h => h.trans hx

@[expose] def ModelVertex (w : ↥P1408) : Prop :=
  In2A w ∧ w * pB ≠ pB * w ∧ orderOf (pB * w) ≠ 5 ∧ (orderOf (pB * w) = 4 → In2A ((pB * w) ^ 2))

theorem ModelVertex.map_conj {w : ↥P1408} (hw : ModelVertex w) {x : ↥P1408}
    (hx : x * pB * x⁻¹ = pB) : ModelVertex (x * w * x⁻¹) := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  have hφ : MulAut.conj x pB = pB := hx
  have hmul : pB * MulAut.conj x w = MulAut.conj x (pB * w) := by rw [map_mul, hφ]
  show ModelVertex (MulAut.conj x w)
  refine ⟨h1.map_conj x, fun hc => h2 ?_, ?_, fun h4' => ?_⟩
  · apply (MulAut.conj x).injective
    rw [map_mul, map_mul, hφ]
    exact hc
  · rw [hmul, MulEquiv.orderOf_eq]
    exact h3
  · rw [hmul, MulEquiv.orderOf_eq] at h4'
    rw [hmul, ← map_pow]
    exact (h4 h4').map_conj x

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
