module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Tools

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup CFSG.Assembly.LowTwoRank

@[expose] def HasWit {Y : Type} [Group Y] (a : MulAut Y) : Prop :=
  ∃ x y : Y, a x = x ∧ a y = y ∧ Odd (orderOf x) ∧ 2 ∣ orderOf (x * y * x⁻¹ * y⁻¹)

theorem HasWit.conj {Y : Type} [Group Y] {a : MulAut Y} (h : HasWit a) (φ : MulAut Y) :
    HasWit (φ * a * φ⁻¹) := by
  obtain ⟨x, y, hx, hy, hxo, hc⟩ := h
  refine ⟨φ x, φ y, ?_, ?_, ?_, ?_⟩
  · change φ (a (φ⁻¹ (φ x))) = φ x
    rw [MulAut.inv_apply_self, hx]
  · change φ (a (φ⁻¹ (φ y))) = φ y
    rw [MulAut.inv_apply_self, hy]
  · rw [MulEquiv.orderOf_eq]
    exact hxo
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, MulEquiv.orderOf_eq]
    exact hc

theorem HasWit.congr {Y Y' : Type} [Group Y] [Group Y'] {a : MulAut Y} (h : HasWit a)
    (e : Y ≃* Y') : HasWit (MulAut.congr e a) := by
  obtain ⟨x, y, hx, hy, hxo, hc⟩ := h
  refine ⟨e x, e y, ?_, ?_, ?_, ?_⟩
  · change e (a (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx]
  · change e (a (e.symm (e y))) = e y
    rw [MulEquiv.symm_apply_apply, hy]
  · rw [MulEquiv.orderOf_eq]
    exact hxo
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, MulEquiv.orderOf_eq]
    exact hc

theorem not_isPGroup_of_hasWit {Y : Type} [Group Y] [Finite Y] {a : MulAut Y} (h : HasWit a) :
    ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) := by
  obtain ⟨x, y, hx, hy, hxo, hc⟩ := h
  have hxF : x ∈ fixedPoints a := mem_fixedPoints.mpr hx
  have hyF : y ∈ fixedPoints a := mem_fixedPoints.mpr hy
  refine not_isPGroup_of_closure_odd (T := {x, y * x * y⁻¹}) ?_ ?_ ?_
  · rintro t (rfl | rfl)
    · exact hxF
    · exact mul_mem (mul_mem hyF hxF) (inv_mem hyF)
  · rintro t (rfl | rfl)
    · exact hxo
    · have := MulEquiv.orderOf_eq (MulAut.conj y) x
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hxo
  · have h1 : x ∈ closure ({x, y * x * y⁻¹} : Set Y) := subset_closure (Or.inl rfl)
    have h2 : y * x * y⁻¹ ∈ closure ({x, y * x * y⁻¹} : Set Y) :=
      subset_closure (Or.inr rfl)
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ closure ({x, y * x * y⁻¹} : Set Y) := by
      have e : x * y * x⁻¹ * y⁻¹ = x * (y * x * y⁻¹)⁻¹ := by group
      rw [e]
      exact mul_mem h1 (inv_mem h2)
    exact hc.trans (Subgroup.orderOf_dvd_natCard _ hmem)

theorem twoNilpFor_of_hasWit {C : (Y : Type) → [Group Y] → Prop}
    (h : ∀ (Y : Type) [Group Y] [Finite Y], C Y → IsSimpleGroup Y → ∀ a : MulAut Y,
      orderOf a = 2 → IsTwoNilpExc Y ∨ HasWit a) : TwoNilpFor C := by
  intro Y _ _ hY hs _ a ha hP
  rcases h Y hY hs a ha with h | h
  · exact h
  · exact absurd hP (not_isPGroup_of_hasWit h)

@[expose] def PSURow : Prop :=
  TwoNilpFor fun Y _ => ∃ n f : ℕ, StatedClassicalModel Y .PSU n 2 f

@[expose] def POmegaPlusRow : Prop :=
  TwoNilpFor fun Y _ => ∃ n f : ℕ, StatedClassicalModel Y .POmegaPlus n 2 f

@[expose] def POmegaMinusRow : Prop :=
  TwoNilpFor fun Y _ => ∃ n f : ℕ, StatedClassicalModel Y .POmegaMinus n 2 f

end CFSG.ComponentClassification.HarrisLit.L33.C2
