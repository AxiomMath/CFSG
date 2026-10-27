module

public import CFSG.ClassicalGroups.Alternating.PointRadicalFixed
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.ClassicalGroups.Alternating

open CFSG.LocalAnalysis.ComponentInitial
open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

theorem Lsp_ne_bot (hB : B.IsAlt) (hBn : B.Nondegenerate) {u : V} (hu : u ≠ 0) :
    Lsp B hB u ≠ ⊥ := by
  obtain ⟨x, hx⟩ : ∃ x, B x u ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (hBn.2 u h)
  intro hbot
  have hmem : (⟨symplecticTransvection B hB u 1,
      symplecticTransvection_mem_bilinIsometryGroup hB u 1⟩ : Gsp B) ∈ Lsp B hB u :=
    symplecticTransvection_mem_pointRadical hB u 1
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 := congrArg (fun g : Gsp B => g.app x) hmem
  simp only [Gsp.app, Subgroup.coe_one, symplecticTransvection_apply] at h1
  have h2 : B x u • u = 0 := by
    have h3 : x + B x u • u = x := by simpa using h1
    simpa using h3
  exact hx ((smul_eq_zero.mp h2).resolve_right hu)

theorem Lsp_inf_ne_bot_of_B_eq_zero (hB : B.IsAlt) (hBn : B.Nondegenerate) {u u' : V}
    (hu : u ≠ 0) (hu' : u' ≠ 0) (h : B u u' = 0) : Lsp B hB u ⊓ Lsp B hB u' ≠ ⊥ := by
  by_cases hmul : ∃ s : K, s ≠ 0 ∧ u' = s • u
  · obtain ⟨s, hs, rfl⟩ := hmul
    rw [Lsp_smul hB hs, inf_idem]
    exact Lsp_ne_bot hB hBn hu
  · push Not at hmul
    have h' : B u' u = 0 := by rw [← hB.neg_eq u u', h, neg_zero]
    have hsw : siegel B hB u u' 0 = siegel B hB u' u 0 := by
      refine Units.ext (LinearMap.ext fun y => ?_)
      rw [siegel_apply hB h, siegel_apply hB h']
      simp only [zero_mul, zero_smul, add_zero]
      abel
    set g : Gsp B := ⟨siegel B hB u u' 0, siegel_mem_bilinIsometryGroup hB u u' 0⟩ with hg
    have hg1 : g ∈ Lsp B hB u := siegel_mem_pointRadical hB h 0
    have hg2 : g ∈ Lsp B hB u' := by
      show siegel B hB u u' 0 ∈ pointRadical B hB u'
      rw [hsw]
      exact siegel_mem_pointRadical hB h' 0
    intro hbot
    have hg3 : g ∈ Lsp B hB u ⊓ Lsp B hB u' := ⟨hg1, hg2⟩
    rw [hbot, Subgroup.mem_bot] at hg3
    have hy : ∀ y : V, B y u • u' + B y u' • u = 0 := by
      intro y
      have h1 := congrArg (fun g : Gsp B => g.app y) hg3
      simp only [hg, Gsp.app, Subgroup.coe_one] at h1
      rw [siegel_apply hB h] at h1
      simp only [zero_mul, zero_smul, add_zero, Units.val_one, Module.End.one_apply] at h1
      have h2 : B y u • u' + B y u' • u = 0 := by
        have := h1
        rw [add_assoc] at this
        simpa using this
      exact h2
    refine hu (hBn.2 u fun y => ?_)
    by_contra hne
    apply hmul (-(B y u' / B y u)) (by
      intro h0
      have : B y u' = 0 := by
        have := neg_eq_zero.mp h0
        rw [div_eq_zero_iff] at this
        exact this.resolve_right hne
      have h3 := hy y
      rw [this, zero_smul, add_zero] at h3
      exact hu' ((smul_eq_zero.mp h3).resolve_left hne))
    have h3 := hy y
    have h4 : u' = -(B y u' / B y u) • u := by
      have : B y u • u' = -(B y u' • u) := eq_neg_of_add_eq_zero_left h3
      calc u' = (B y u)⁻¹ • (B y u • u') := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
        _ = (B y u)⁻¹ • (-(B y u' • u)) := by rw [this]
        _ = -(B y u' / B y u) • u := by
          rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
    exact h4

theorem Lsp_inf_eq_bot_iff (hB : B.IsAlt) (hBn : B.Nondegenerate) {u u' : V} (hu : u ≠ 0)
    (hu' : u' ≠ 0) : Lsp B hB u ⊓ Lsp B hB u' = ⊥ ↔ B u u' ≠ 0 := by
  constructor
  · intro h hzero
    exact Lsp_inf_ne_bot_of_B_eq_zero hB hBn hu hu' hzero h
  · intro h
    rw [eq_bot_iff]
    rintro g ⟨hg1, hg2⟩
    have hinf : (g : LinearMap.GeneralLinearGroup K V) ∈
        pointRadical B hB u' ⊓ pointRadical B hB u := ⟨hg2, hg1⟩
    rw [pointRadical_inf_eq_bot hB h, Subgroup.mem_bot] at hinf
    exact Subgroup.mem_bot.mpr (Subtype.ext hinf)

end CFSG.ClassicalGroups.Alternating
