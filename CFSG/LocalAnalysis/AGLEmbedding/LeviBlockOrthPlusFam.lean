module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSubspaceCount

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {K : Type} [Field K]

@[expose] def plusFamOne (p : Fin 2 → K) : Submodule K (Fin 2 ⊕ Fin 2 → K) where
  carrier := {x | x (Sum.inl 0) * p 1 = x (Sum.inr 1) * p 0 ∧
    x (Sum.inl 1) * p 1 = x (Sum.inr 0) * p 0}
  add_mem' := fun {a b} ha hb => ⟨by simp only [Pi.add_apply]; linear_combination ha.1 + hb.1,
    by simp only [Pi.add_apply]; linear_combination ha.2 + hb.2⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := fun c x hx =>
    ⟨by simp only [Pi.smul_apply, smul_eq_mul]; linear_combination c * hx.1,
      by simp only [Pi.smul_apply, smul_eq_mul]; linear_combination c * hx.2⟩

@[expose] def plusFamTwo (p : Fin 2 → K) : Submodule K (Fin 2 ⊕ Fin 2 → K) where
  carrier := {x | x (Sum.inl 0) * p 1 = x (Sum.inl 1) * p 0 ∧
    x (Sum.inr 1) * p 1 = x (Sum.inr 0) * p 0}
  add_mem' := fun {a b} ha hb => ⟨by simp only [Pi.add_apply]; linear_combination ha.1 + hb.1,
    by simp only [Pi.add_apply]; linear_combination ha.2 + hb.2⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := fun c x hx =>
    ⟨by simp only [Pi.smul_apply, smul_eq_mul]; linear_combination c * hx.1,
      by simp only [Pi.smul_apply, smul_eq_mul]; linear_combination c * hx.2⟩

theorem mem_plusFamOne {p : Fin 2 → K} {x : Fin 2 ⊕ Fin 2 → K} :
    x ∈ plusFamOne p ↔ x (Sum.inl 0) * p 1 = x (Sum.inr 1) * p 0 ∧
      x (Sum.inl 1) * p 1 = x (Sum.inr 0) * p 0 :=
  Iff.rfl

theorem mem_plusFamTwo {p : Fin 2 → K} {x : Fin 2 ⊕ Fin 2 → K} :
    x ∈ plusFamTwo p ↔ x (Sum.inl 0) * p 1 = x (Sum.inl 1) * p 0 ∧
      x (Sum.inr 1) * p 1 = x (Sum.inr 0) * p 0 :=
  Iff.rfl

theorem mem_plusFamOne_one_zero {x : Fin 2 ⊕ Fin 2 → K} :
    x ∈ plusFamOne ![1, 0] ↔ x (Sum.inr 0) = 0 ∧ x (Sum.inr 1) = 0 := by
  simp only [mem_plusFamOne, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    mul_zero, mul_one]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2.symm, h1.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2.symm, h1.symm⟩

theorem flag_two_eq_plusFamOne : flag 2 K 2 = plusFamOne ![1, 0] := by
  ext x
  rw [mem_plusFamOne_one_zero, mem_flag]
  constructor
  · rintro ⟨h, -⟩
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩
    refine ⟨fun j => ?_, fun j hj => absurd j.isLt (by omega)⟩
    fin_cases j
    · exact h0
    · exact h1

theorem plusFamTwo_smul {c : K} (hc : c ≠ 0) (p : Fin 2 → K) :
    plusFamTwo (c • p) = plusFamTwo p := by
  ext x
  simp only [mem_plusFamTwo, Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨mul_left_cancel₀ hc ?_, mul_left_cancel₀ hc ?_⟩
    · linear_combination h1
    · linear_combination h2
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination c * h1, by linear_combination c * h2⟩

theorem polar_quadPlus_two (w v : Fin 2 ⊕ Fin 2 → K) :
    polar (quadPlus 2 K) w v = w (Sum.inl 0) * v (Sum.inr 0) + w (Sum.inr 0) * v (Sum.inl 0) +
      (w (Sum.inl 1) * v (Sum.inr 1) + w (Sum.inr 1) * v (Sum.inl 1)) := by
  simp only [polar, quadPlus_apply, Fin.sum_univ_two, Pi.add_apply]
  ring

theorem quadPlus_two_apply (x : Fin 2 ⊕ Fin 2 → K) :
    quadPlus 2 K x = x (Sum.inl 0) * x (Sum.inr 0) + x (Sum.inl 1) * x (Sum.inr 1) := by
  rw [quadPlus_apply, Fin.sum_univ_two]

variable [CharP K 2]

theorem plusFamTwo_isotropic {p : Fin 2 → K} (hp : p ≠ 0) {x : Fin 2 ⊕ Fin 2 → K}
    (hx : x ∈ plusFamTwo p) : quadPlus 2 K x = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨h1, h3⟩ := mem_plusFamTwo.1 hx
  rw [quadPlus_two_apply]
  have hp' : p 0 ≠ 0 ∨ p 1 ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hp (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  rcases hp' with hp0 | hp1
  · refine mul_left_cancel₀ hp0 ?_
    linear_combination -x (Sum.inl 0) * h3 - x (Sum.inr 1) * h1 +
      x (Sum.inl 0) * x (Sum.inr 1) * p 1 * h2
  · refine mul_left_cancel₀ hp1 ?_
    linear_combination x (Sum.inr 0) * h1 + x (Sum.inl 1) * h3 +
      x (Sum.inl 1) * x (Sum.inr 0) * p 0 * h2

theorem plusFamTwo_le_of_isotropic {p : Fin 2 → K} {P : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hP : ∀ x ∈ P, quadPlus 2 K x = 0) (hv : (Sum.elim p 0 : Fin 2 ⊕ Fin 2 → K) ∈ P)
    (hX : ¬ P ≤ plusFamOne ![1, 0]) : P ≤ plusFamTwo p := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have key : ∀ w ∈ P, w ∉ plusFamOne ![1, 0] → w ∈ plusFamTwo p := by
    intro w hw hwX
    rw [mem_plusFamOne_one_zero, not_and_or] at hwX
    have hpol : polar (quadPlus 2 K) w (Sum.elim p 0) = 0 := by
      rw [polar, hP _ (P.add_mem hw hv), hP w hw, hP _ hv]
      ring
    rw [polar_quadPlus_two] at hpol
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, zero_add] at hpol
    have hQ := hP w hw
    rw [quadPlus_two_apply] at hQ
    have hf : w (Sum.inr 1) * p 1 = w (Sum.inr 0) * p 0 := by
      linear_combination hpol - w (Sum.inr 0) * p 0 * h2
    refine ⟨?_, hf⟩
    have e1 : (w (Sum.inl 0) * p 1 - w (Sum.inl 1) * p 0) * w (Sum.inr 0) = 0 := by
      linear_combination p 1 * hQ + w (Sum.inl 1) * hf -
        w (Sum.inl 1) * w (Sum.inr 1) * p 1 * h2
    have e2 : (w (Sum.inl 0) * p 1 - w (Sum.inl 1) * p 0) * w (Sum.inr 1) = 0 := by
      linear_combination -(p 0) * hQ + w (Sum.inl 0) * hf +
        w (Sum.inl 0) * w (Sum.inr 0) * p 0 * h2
    rcases hwX with h0 | h1
    · exact sub_eq_zero.1 ((mul_eq_zero.1 e1).resolve_right h0)
    · exact sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_right h1)
  obtain ⟨w₀, hw₀, hw₀X⟩ := Set.not_subset.1 hX
  intro w hw
  by_cases hwX : w ∈ plusFamOne ![1, 0]
  · have h1 := key _ (P.add_mem hw hw₀) fun h => hw₀X (by
      have := (plusFamOne (![1, 0] : Fin 2 → K)).sub_mem h hwX
      rwa [add_sub_cancel_left] at this)
    have := (plusFamTwo p).sub_mem h1 (key w₀ hw₀ hw₀X)
    rwa [add_sub_cancel_right] at this
  · exact key w hw hwX

end CFSG.AGLEmbedding.LeviBlock
