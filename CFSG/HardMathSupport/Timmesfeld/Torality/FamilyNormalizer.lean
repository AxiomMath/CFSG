module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2Split

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.TwE6Step3

variable {τ : Tag} {K : Type} [Field K] {ι : Type}

section Certificates

theorem familyGroup_le_normalizer_rootSpan_of_subset (a : ι → Fin τ.rank → Kˣ)
    {S : Set (Fin τ.rank → ℤ)} (hS : S ⊆ familyKernel a)
    (hcomm : ∀ α ∈ familyKernel a \ S, ∀ β ∈ S, ∀ x ∈ rootSubgroup τ K α,
      ∀ y ∈ rootSubgroup τ K β, Commute x y) :
    familyGroup (K := K) a ≤
      Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) := by
  have hSroot : ∀ α ∈ S, IsRoot τ α := fun α hα => (hS hα).1
  rw [familyGroup]
  refine sup_le (torusGroup_le_normalizer_rootSpan hSroot) ?_
  refine iSup₂_le fun α hα => ?_
  by_cases hαS : α ∈ S
  · exact (le_iSup₂_of_le (f := fun β (_ : β ∈ S) => rootSubgroup τ K β) α hαS le_rfl).trans
      Subgroup.le_normalizer
  · have hcent : rootSpan τ K (familyKernel a \ S) ≤
        Subgroup.centralizer (rootSpan τ K S : Set (ModGL τ K)) := by
      rw [Subgroup.le_centralizer_iff]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro g' hg'
      exact rootSpan_commute hcomm hg' hy
    exact (le_iSup₂_of_le (f := fun β (_ : β ∈ familyKernel a \ S) => rootSubgroup τ K β) α
      ⟨hα, hαS⟩ le_rfl).trans (hcent.trans (Subgroup.centralizer_le_normalizer _))

theorem canonicalRep_mem_normalizer_rootSpan_of_mapsTo {S : Set (Fin τ.rank → ℤ)}
    {w : WeylGroup τ} (hS : ∀ α ∈ S, IsRoot τ α ∧ w • α ∈ S)
    (hS' : ∀ α ∈ S, IsRoot τ α ∧ w⁻¹ • α ∈ S) :
    canonicalRep (coxeterSystem τ) K w ∈
      Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) := by
  refine Subgroup.mem_normalizer_iff.2 fun y => ⟨?_, ?_⟩
  · intro hy
    exact canonicalRep_conj_mem_rootSpan (K := K) w hS hy
  · intro hy
    have hconj := canonicalRep_inv_conj_mem_rootSpan (K := K) w hS' hy
    have heq : (canonicalRep (coxeterSystem τ) K w)⁻¹ *
        (canonicalRep (coxeterSystem τ) K w * y *
          (canonicalRep (coxeterSystem τ) K w)⁻¹) *
          canonicalRep (coxeterSystem τ) K w = y := by group
    rwa [heq] at hconj

theorem familyCentralizer_le_normalizer_rootSpan_of_subset (a : ι → Fin τ.rank → Kˣ)
    {S : Set (Fin τ.rank → ℤ)} (hS : S ⊆ familyKernel a)
    (hstab : ∀ w ∈ familyStabilizer a, ∀ α ∈ S, w • α ∈ S)
    (hcomm : ∀ α ∈ familyKernel a \ S, ∀ β ∈ S, ∀ x ∈ rootSubgroup τ K α,
      ∀ y ∈ rootSubgroup τ K β, Commute x y) :
    familyCentralizer τ K a ≤
      Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) := by
  intro g hg
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul τ K a hg
  have hmN := familyGroup_le_normalizer_rootSpan_of_subset a hS hcomm hm
  have hwN : canonicalRep (coxeterSystem τ) K w ∈
      Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) :=
    canonicalRep_mem_normalizer_rootSpan_of_mapsTo
      (fun α hα => ⟨(hS hα).1, hstab w hw α hα⟩)
      (fun α hα => ⟨(hS hα).1, hstab w⁻¹ (familyStabilizer_inv hw) α hα⟩)
  exact mul_mem hmN hwN

theorem familyCentralizer_le_normalizer_rootSpan (a : ι → Fin τ.rank → Kˣ) :
    familyCentralizer τ K a ≤
      Subgroup.normalizer (rootSpan τ K (familyKernel a) : Set (ModGL τ K)) := by
  refine familyCentralizer_le_normalizer_rootSpan_of_subset a (subset_refl _)
    (fun w hw α hα => ?_) (fun α hα => ?_)
  · rw [← image_familyKernel hw]
    exact ⟨α, hα, rfl⟩
  · exact absurd hα.1 hα.2

end Certificates

end CFSG.HardMathSupport.Timmesfeld.Torality
