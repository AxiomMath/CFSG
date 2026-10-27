module

public import CFSG.CGT.PushingUpLit.LIT.A4.SECSplit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingTheorem
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover

public section

namespace CFSG.CGT.PushingUpLit.SEC

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.CGT.PushingUpLit.A4
open CFSG.ComponentClassification.AschbacherStrongEmbedding
open CFSG.ComponentClassification.AschbacherTightEmbedding

theorem fusionStronglyEmbedded_of_criterion_hyps {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (hM : M ≠ ⊤) {D : Set G} (hD2 : ∀ d ∈ D, orderOf d = 2)
    (hDn : ∀ d ∈ D, ∀ g : G, g⁻¹ * d * g ∈ D)
    (h1 : ∀ x ∈ D, x ∈ M → ∀ g : G, g⁻¹ * x * g ∈ M → g ∈ M)
    (h2 : ∀ x ∈ D, x ∈ M → ∀ y ∈ D, y ∈ M → x * y = y * x → ∀ g : G,
      g⁻¹ * (x * y) * g ≠ 1 → g⁻¹ * (x * y) * g ∈ M → g ∈ M)
    {x : G} (hx : x ∈ D) (hxM : x ∈ M) (hO : NoTwoQuotient ↥(Subgroup.normalClosure {x})) :
    fusionStronglyEmbedded
      ((M ⊓ Subgroup.normalClosure {x}).subgroupOf (Subgroup.normalClosure {x})) := by
  have hz : orderOf x = 2 := hD2 x hx
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hz, pow_two] at this
  have huniq : ∀ g : G, x ∈ rightConjugate M g ↔ g ∈ M := by
    intro g
    rw [mem_rightConjugate_iff]
    constructor
    · intro hg
      have := h1 x hx hxM g⁻¹ (by simpa using hg)
      simpa using M.inv_mem this
    · intro hg
      exact M.mul_mem (M.mul_mem hg hxM) (M.inv_mem hg)
  have hPUC : ProductUniqueContainment M x := by
    intro t ht hcomm hne g
    obtain ⟨c, rfl⟩ := ht
    have htD : CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x c ∈ D := hDn x hx c
    have htM : CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x c ∈ M :=
      centralizer_le_of_unique huniq (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq.symm)
    refine ⟨fun hmem => ?_, fun hg => ?_⟩
    · refine h2 x hx hxM _ htD htM hcomm.eq g ?_ hmem
      intro h1'
      have hxt : x * CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x c = 1 := by
        have := congrArg (fun w => g * w * g⁻¹) h1'
        simpa [mul_assoc] using this
      exact hne ((eq_inv_of_mul_eq_one_right hxt).trans (inv_eq_of_mul_eq_one_right hxx))
    · exact M.mul_mem (M.mul_mem (M.inv_mem hg) (M.mul_mem hxM htM)) hg
  obtain ⟨h12, h23, -⟩ := theorem_3_3 not_minimalInvolutionPointLocalFailure
    benderDoubleCoverRigidity M x hz hM huniq
  have h3 := h23 (h12 hPUC)
  have hO' : NoTwoQuotient ↥(involutionPointHull x) := by
    rw [minimalLocalFailure_hull_eq_normalClosure]
    exact hO
  have hse := fusionStronglyEmbedded_of_pointHullStrongSplit hz hM huniq hO' h3
  rw [minimalLocalFailure_hull_eq_normalClosure] at hse
  rwa [Subgroup.inf_subgroupOf_right]

theorem fusionStronglyEmbedded_of_isSimpleGroup {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {M : Subgroup G} (hM : M ≠ ⊤) {D : Set G} (hD2 : ∀ d ∈ D, orderOf d = 2)
    (hDn : ∀ d ∈ D, ∀ g : G, g⁻¹ * d * g ∈ D)
    (h1 : ∀ x ∈ D, x ∈ M → ∀ g : G, g⁻¹ * x * g ∈ M → g ∈ M)
    (h2 : ∀ x ∈ D, x ∈ M → ∀ y ∈ D, y ∈ M → x * y = y * x → ∀ g : G,
      g⁻¹ * (x * y) * g ≠ 1 → g⁻¹ * (x * y) * g ∈ M → g ∈ M)
    {x : G} (hx : x ∈ D) (hxM : x ∈ M) : fusionStronglyEmbedded M := by
  have hz : orderOf x = 2 := hD2 x hx
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hz; omega
  have hcl : Subgroup.normalClosure ({x} : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({x} : Set G))
      with h | h
    · exact absurd (Subgroup.mem_bot.mp
        (h ▸ Subgroup.subset_normalClosure (Set.mem_singleton x))) hx1
    · exact h
  have hNG : NoTwoQuotient G := noTwoQuotient_of_isSimpleGroup hM hxM hz
  have hO : NoTwoQuotient ↥(Subgroup.normalClosure ({x} : Set G)) := by
    rw [hcl]
    exact noTwoQuotient_of_mulEquiv Subgroup.topEquiv.symm hNG
  have hse := fusionStronglyEmbedded_of_criterion_hyps hM hD2 hDn h1 h2 hx hxM hO
  rw [hcl, inf_top_eq] at hse
  exact fusionStronglyEmbedded_of_subgroupOf_top' hse

end CFSG.CGT.PushingUpLit.SEC
