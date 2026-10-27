module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCollapse

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open
open CFSG.ClassicalInvolution.Balance (oddCoreIn)
open scoped commutatorElement

section System

variable {F : Type} [Group F] [Finite F]

theorem a7SystemMod_of_lt {n : ℕ} (hB : CITBelow2A7 n) {Y' Y : Subgroup F} (hYY' : Y ≤ Y')
    (hlt : Nat.card Y < n) {Λ : Set (Subgroup F)} (hne : Λ.Nonempty) (hY : ⨆ L ∈ Λ, L = Y)
    (hinv : ∀ y ∈ Y, ∀ L ∈ Λ, L.map (MulAut.conj y).toMonoidHom ∈ Λ)
    (hcls : ∀ L ∈ Λ, ∃ u : F, IsClassical2A7 Y' L u) : A7SystemMod (restrictTo Λ Y) :=
  hB ↥Y hlt _ (inClass2A7_restrictTo_rel hYY' hne hY hinv hcls)

variable {Y : Subgroup F} {Λ : Set (Subgroup F)} (hS : A7SystemMod (restrictTo Λ Y))
  (hY : ⨆ L ∈ Λ, L = Y)

include hS

omit hY in
theorem exists_component_of_system {L : Subgroup F} (hL : L ∈ Λ) :
    ∃ (Φ : Set (Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y)))
      (D : A7SystemData (↥Y ⧸ classicalInvolutionOddCore ↥Y) Φ) (i : Fin D.card),
      D.comp i = (L.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) := by
  obtain ⟨D⟩ := hS
  have hmem : (L.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) ∈
      oddQuotientFamily2A7 (restrictTo Λ Y) := ⟨_, ⟨L, hL, rfl⟩, rfl⟩
  rw [D.members] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact ⟨_, D, i, hi⟩

include hY

theorem commutator_mem_oddCoreIn_of_system {L : Subgroup F} (hL : L ∈ Λ) {u : F} (huL : u ∈ L)
    (hu : ∀ a ∈ L, a * u = u * a) {y : F} (hy : y ∈ Y) :
    u * y * u⁻¹ * y⁻¹ ∈ oddCoreIn Y := by
  obtain ⟨Φ, D, i, hi⟩ := exists_component_of_system hS hL
  have hLY : L ≤ Y := le_of_mem_of_iSup_eq hY hL
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  set uY : ↥Y := ⟨u, hLY huL⟩ with huY
  have huc : π uY ∈ D.comp i := by
    rw [hi]
    exact ⟨uY, Subgroup.mem_subgroupOf.mpr huL, rfl⟩
  have hcomm : ∀ q ∈ (⨆ k, D.comp k : Subgroup _), π uY * q = q * π uY := by
    intro q hq
    induction hq using Subgroup.iSup_induction' with
    | hp k q hq =>
      by_cases hki : k = i
      · subst hki
        rw [hi] at hq
        obtain ⟨a, ha, rfl⟩ := hq
        have hau : a * uY = uY * a := Subtype.ext (hu (a : F) (Subgroup.mem_subgroupOf.mp ha))
        show π uY * π a = π a * π uY
        rw [← map_mul, ← map_mul, ← hau]
      · exact D.commute i k (Ne.symm hki) _ huc q hq
    | h1 => simp
    | hmul x y _ _ hx hy =>
      rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  have hyq : π ⟨y, hy⟩ ∈ (⨆ k, D.comp k : Subgroup _) := by
    rw [D.generate]
    trivial
  have h1 := hcomm _ hyq
  refine ⟨⟨u * y * u⁻¹ * y⁻¹, ?_⟩, ?_, rfl⟩
  · exact Y.mul_mem (Y.mul_mem (Y.mul_mem (hLY huL) hy) (Y.inv_mem (hLY huL))) (Y.inv_mem hy)
  · apply (QuotientGroup.eq_one_iff _).mp
    show π (uY * ⟨y, hy⟩ * uY⁻¹ * ⟨y, hy⟩⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group

theorem images_eq_or_commute_of_system {L M : Subgroup F} (hL : L ∈ Λ) (hM : M ∈ Λ) :
    (L.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) =
        (M.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) ∨
      ∀ a ∈ L, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn Y := by
  obtain ⟨D⟩ := hS
  have hLY : L ≤ Y := le_of_mem_of_iSup_eq hY hL
  have hMY : M ≤ Y := le_of_mem_of_iSup_eq hY hM
  have hmemL : (L.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) ∈
      oddQuotientFamily2A7 (restrictTo Λ Y) := ⟨_, ⟨L, hL, rfl⟩, rfl⟩
  have hmemM : (M.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) ∈
      oddQuotientFamily2A7 (restrictTo Λ Y) := ⟨_, ⟨M, hM, rfl⟩, rfl⟩
  rw [D.members] at hmemL hmemM
  obtain ⟨i, hi⟩ := hmemL
  obtain ⟨j, hj⟩ := hmemM
  by_cases hij : i = j
  · subst hij
    exact Or.inl (hi.symm.trans hj)
  · refine Or.inr fun a ha b hb => ?_
    have hai : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨a, hLY ha⟩ ∈ D.comp i := by
      rw [hi]
      exact ⟨⟨a, hLY ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hbj : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨b, hMY hb⟩ ∈ D.comp j := by
      rw [hj]
      exact ⟨⟨b, hMY hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have h1 := D.commute i j hij _ hai _ hbj
    refine ⟨⟨a * b * a⁻¹ * b⁻¹, Y.mul_mem (Y.mul_mem (Y.mul_mem (hLY ha) (hMY hb))
      (Y.inv_mem (hLY ha))) (Y.inv_mem (hMY hb))⟩, ?_, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
    show π (⟨a, hLY ha⟩ * ⟨b, hMY hb⟩ * (⟨a, hLY ha⟩ : ↥Y)⁻¹ * (⟨b, hMY hb⟩ : ↥Y)⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group

end System

end CFSG.ClassicalInvolution.Hat2A7
