module

public import CFSG.GH74.GLS.Bg.Pu5.LPTPAbs

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Abstract

variable {H : Type} [Group H]

theorem conj_swapDiag_of_commute {A : Subgroup H} {s : H} (hAB : ⁅A, conjSub s⁻¹ A⁆ = ⊥) {g : H}
    (hgs : g * s = s * g) (x : A) (hy : g * (x : H) * g⁻¹ ∈ A) :
    g * swapDiag hAB x * g⁻¹ = swapDiag hAB ⟨g * x * g⁻¹, hy⟩ := by
  have h1 : g * s * g⁻¹ = s := by rw [hgs]; group
  have h2 : g * s⁻¹ * g⁻¹ = s⁻¹ := by
    have := (Commute.inv_right (show Commute g s from hgs)).eq
    rw [this]; group
  rw [swapDiag_apply, swapDiag_apply]
  show g * ((x : H) * (s⁻¹ * x * s)) * g⁻¹ = (g * x * g⁻¹) * (s⁻¹ * (g * x * g⁻¹) * s)
  calc g * ((x : H) * (s⁻¹ * x * s)) * g⁻¹
      = (g * x * g⁻¹) * ((g * s⁻¹ * g⁻¹) * (g * x * g⁻¹) * (g * s * g⁻¹)) := by group
    _ = _ := by rw [h1, h2]

theorem mem_normalizer_range_swapDiag {A : Subgroup H} {s : H} (hAB : ⁅A, conjSub s⁻¹ A⁆ = ⊥)
    {g : H} (hgs : g * s = s * g) (hgA : g ∈ normalizer (A : Set H)) :
    g ∈ normalizer ((swapDiag hAB).range : Set H) := by
  have key : ∀ g' : H, g' * s = s * g' → g' ∈ normalizer (A : Set H) →
      ∀ d ∈ (swapDiag hAB).range, g' * d * g'⁻¹ ∈ (swapDiag hAB).range := by
    rintro g' hg's hg'A _ ⟨x, rfl⟩
    have hy : g' * (x : H) * g'⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hg'A x).1 x.2
    exact ⟨⟨g' * x * g'⁻¹, hy⟩, (conj_swapDiag_of_commute hAB hg's x hy).symm⟩
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · exact key g hgs hgA d
  · intro hd
    have hgs' : g⁻¹ * s = s * g⁻¹ := ((show Commute g s from hgs).inv_left).eq
    have := key g⁻¹ hgs' (inv_mem hgA) _ hd
    simpa [mul_assoc] using this

theorem commute_of_commute_swapDiag {A : Subgroup H} (hA : CFSG.IsQuasisimple ↥A) {s : H}
    (hAB : ⁅A, conjSub s⁻¹ A⁆ = ⊥) {g : H} (hgs : g * s = s * g) (hgA : g ∈ normalizer (A : Set H))
    (hgD : ∀ w ∈ (swapDiag hAB).range, w * g = g * w) : ∀ a ∈ A, a * g = g * a := by
  have hcomm : ∀ x ∈ A, ∀ y ∈ conjSub s⁻¹ A, x * y = y * x := fun x hx y hy =>
    commute_of_commutator_conj_eq_bot hAB hx hy
  have hconjA : ∀ q ∈ A, g * q * g⁻¹ ∈ A := fun q hq => (Subgroup.mem_normalizer_iff.1 hgA q).1 hq
  have hcQ : ∀ q ∈ A, ⁅q, g⁆ ∈ A := by
    intro q hq
    have h1 : g * q⁻¹ * g⁻¹ ∈ A := hconjA _ (A.inv_mem hq)
    have : ⁅q, g⁆ = q * (g * q⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact A.mul_mem hq h1
  have hB : ∀ q ∈ A, ⁅q, g⁆ ∈ conjSub s⁻¹ A := by
    intro q hq
    have hY : g * q * g⁻¹ ∈ A := hconjA q hq
    have hdiag := conj_swapDiag_of_commute hAB hgs ⟨q, hq⟩ hY
    have hqD := hgD (swapDiag hAB ⟨q, hq⟩) ⟨⟨q, hq⟩, rfl⟩
    have hqq : q * (s⁻¹ * q * s) = (g * q * g⁻¹) * (s⁻¹ * (g * q * g⁻¹) * s) := by
      have h1 : g * swapDiag hAB ⟨q, hq⟩ * g⁻¹ = swapDiag hAB ⟨q, hq⟩ := by
        rw [← hqD]; group
      have h2 := hdiag.symm.trans h1
      rw [swapDiag_apply, swapDiag_apply] at h2
      exact h2.symm
    have hq' : s⁻¹ * q * s ∈ conjSub s⁻¹ A := conj_mem_conjSub hq
    have hy' : s⁻¹ * (g * q * g⁻¹) * s ∈ conjSub s⁻¹ A := conj_mem_conjSub hY
    have he : (s⁻¹ * (g * q * g⁻¹) * s) * (s⁻¹ * q * s)⁻¹ ∈ conjSub s⁻¹ A :=
      mul_mem hy' (inv_mem hq')
    have hYe := hcomm _ hY _ he
    have hcom_eq : ⁅q, g⁆ = q * (g * q * g⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [hcom_eq]
    generalize hYdef : g * q * g⁻¹ = Y at hYe hqq hcom_eq he ⊢
    generalize hadef : s⁻¹ * q * s = a at hYe hqq he ⊢
    generalize hbdef : s⁻¹ * Y * s = b at hYe hqq he ⊢
    have h1 : q = Y * (b * a⁻¹) := by
      calc q = (q * a) * a⁻¹ := by group
        _ = (Y * b) * a⁻¹ := by rw [hqq]
        _ = Y * (b * a⁻¹) := by group
    have h2 : q * Y⁻¹ = b * a⁻¹ := by
      calc q * Y⁻¹ = (Y * (b * a⁻¹)) * Y⁻¹ := by rw [← h1]
        _ = ((b * a⁻¹) * Y) * Y⁻¹ := by rw [hYe]
        _ = b * a⁻¹ := by group
    rw [h2]
    exact he
  have hcen : ∀ q ∈ A, ∀ x ∈ A, x * ⁅q, g⁆ = ⁅q, g⁆ * x := fun q hq x hx =>
    hcomm x hx _ (hB q hq)
  exact commute_of_central_commutators hA.1 hcQ hcen

variable [Finite H]

theorem commute_of_odd_commutators_swapDiag {A : Subgroup H} (hA : CFSG.IsQuasisimple ↥A) {s : H}
    (hAB : ⁅A, conjSub s⁻¹ A⁆ = ⊥) {g : H} (hgs : g * s = s * g) (hgA : g ∈ normalizer (A : Set H))
    {M : Subgroup H} (hM : Odd (Nat.card ↥M)) (hcomm : ∀ q ∈ (swapDiag hAB).range, ⁅q, g⁆ ∈ M) :
    ∀ a ∈ A, a * g = g * a := by
  have hAq : CFSG.Assembly.IsQuasisimple A :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hA
  have hDq : CFSG.IsQuasisimple ↥(swapDiag hAB).range :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
      (isQuasisimple_range_swapDiag hAB hAq)
  have hgD := commute_of_odd_commutators hDq (mem_normalizer_range_swapDiag hAB hgs hgA) hM hcomm
  exact commute_of_commute_swapDiag hA hAB hgs hgA hgD

end Abstract

end CFSG.GH74.GLS.Bg.Pu5
