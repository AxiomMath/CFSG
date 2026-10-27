module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Sound

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.SuzN0

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.SuzOddCore
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped commutatorElement

section Cent


theorem centralizer_surv {h : Equiv.Perm (Fin 1782)} (hhM : h ∈ suzM)
    (hconj : h * suzInv 1 * h⁻¹ = zElt) {S : Set (Equiv.Perm (Fin 1782))}
    (hS : ∀ τ ∈ invD 1, (∀ j < 5, τ * gensElt h j = gensElt h j * τ) → τ ∈ S)
    {d : Equiv.Perm (Fin 1782)} (hd : d ∈ suzM) {τ : Equiv.Perm (Fin 1782)}
    (hτ : τ ∈ suzT) (hr : ∀ i < 4, τ * (d * rElt i * d⁻¹) = d * rElt i * d⁻¹ * τ)
    (hw : τ * (d * wElt * d⁻¹) = d * wElt * d⁻¹ * τ) :
    ∃ s ∈ S, τ = d * h * s * (d * h)⁻¹ := by
  set τ'' : Equiv.Perm (Fin 1782) := d⁻¹ * τ * d with hτ''
  set τ' : Equiv.Perm (Fin 1782) := h⁻¹ * τ'' * h with hτ'
  have hcomm : ∀ x : Equiv.Perm (Fin 1782), τ * (d * x * d⁻¹) = d * x * d⁻¹ * τ →
      τ'' * x = x * τ'' := by
    intro x hx
    calc τ'' * x = d⁻¹ * (τ * (d * x * d⁻¹)) * d := by rw [hτ'']; group
      _ = d⁻¹ * (d * x * d⁻¹ * τ) * d := by rw [hx]
      _ = x * τ'' := by rw [hτ'']; group
  have hcent : RR ≤ Subgroup.centralizer ({τ''} : Set (Equiv.Perm (Fin 1782))) := by
    refine RR_le fun i hi => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm _ (hr i hi)).symm
  have hz : τ'' * zElt = zElt * τ'' := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hcent zElt_mem_RR)
    exact this.symm
  have ht1 : τ' * suzInv 1 = suzInv 1 * τ' := by
    have e : suzInv 1 = h⁻¹ * zElt * h := by rw [← hconj]; group
    calc τ' * suzInv 1 = h⁻¹ * (τ'' * zElt) * h := by rw [e, hτ']; group
      _ = h⁻¹ * (zElt * τ'') * h := by rw [hz]
      _ = suzInv 1 * τ' := by rw [e, hτ']; group
  have hmemT : ∀ x ∈ suzM, x ∈ suzT := fun x hx => suzM_le_suzT hx
  have hτ'T : τ' ∈ suzT := by
    rw [hτ', hτ'']
    exact suzT.mul_mem (suzT.mul_mem (suzT.inv_mem (hmemT _ hhM)) (suzT.mul_mem
      (suzT.mul_mem (suzT.inv_mem (hmemT _ hd)) hτ) (hmemT _ hd))) (hmemT _ hhM)
  have hD : τ' ∈ invD 1 := by
    rw [invD_eq_centT (i := 1) (by norm_num)]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 ht1, hτ'T⟩
  have hG : ∀ j < 5, τ' * gensElt h j = gensElt h j * τ' := by
    intro j hj
    have hx : ∀ x : Equiv.Perm (Fin 1782), τ'' * x = x * τ'' →
        τ' * (h⁻¹ * x * h) = h⁻¹ * x * h * τ' := by
      intro x hx
      calc τ' * (h⁻¹ * x * h) = h⁻¹ * (τ'' * x) * h := by rw [hτ']; group
        _ = h⁻¹ * (x * τ'') * h := by rw [hx]
        _ = h⁻¹ * x * h * τ' := by rw [hτ']; group
    by_cases h4 : j < 4
    · simp only [gensElt, h4, ↓reduceIte]
      exact hx _ (hcomm _ (hr j h4))
    · simp only [gensElt, h4, ↓reduceIte]
      exact hx _ (hcomm _ hw)
  refine ⟨τ', hS τ' hD hG, ?_⟩
  rw [hτ', hτ'']
  group

end Cent

end CFSG.EvenSporadicStandard.SuzN0
