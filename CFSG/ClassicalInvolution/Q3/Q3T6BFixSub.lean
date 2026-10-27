module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {F : Type} [Group F]

theorem isSubnormal_inf_conjSub_inf_centralizer {y : F} :
    ∀ {N M : Subgroup F}, IsSubnormal N M → y ∈ Subgroup.normalizer (M : Set F) →
      IsSubnormal (N ⊓ conjSub y N ⊓ Subgroup.centralizer ({y} : Set F))
        (M ⊓ Subgroup.centralizer ({y} : Set F)) := by
  intro N M h
  induction h with
  | refl H =>
    intro hyH
    rw [conjSub_eq_of_mem_normalizer hyH, inf_idem]
    exact IsSubnormal.refl _
  | @step N N₁ M hle hnormal hsub ih =>
    intro hyM
    have hih := ih hyM
    set C : Subgroup F := Subgroup.centralizer ({y} : Set F) with hC
    have hle' : N ⊓ conjSub y N ⊓ C ≤ N₁ ⊓ conjSub y N₁ ⊓ C := by
      intro x hx
      refine ⟨⟨hle hx.1.1, ?_⟩, hx.2⟩
      exact mem_conjSub_iff.mpr (hle (mem_conjSub_iff.mp hx.1.2))
    have hnorm : ((N ⊓ conjSub y N ⊓ C).subgroupOf (N₁ ⊓ conjSub y N₁ ⊓ C)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hle']
      intro n m hn hm
      have hconj : ∀ l ∈ N₁, ∀ p ∈ N, l * p * l⁻¹ ∈ N := fun l hl p hp =>
        (Subgroup.normal_subgroupOf_iff hle).mp hnormal p l hp hl
      refine ⟨⟨hconj m hm.1.1 n hn.1.1, ?_⟩, ?_⟩
      · have h1 : y⁻¹ * m * y ∈ N₁ := mem_conjSub_iff.mp hm.1.2
        have h2 : y⁻¹ * n * y ∈ N := mem_conjSub_iff.mp hn.1.2
        have := hconj _ h1 _ h2
        have e : y⁻¹ * (m * n * m⁻¹) * y = (y⁻¹ * m * y) * (y⁻¹ * n * y) * (y⁻¹ * m * y)⁻¹ := by
          group
        exact mem_conjSub_iff.mpr (e ▸ this)
      · exact C.mul_mem (C.mul_mem hm.2 hn.2) (C.inv_mem hm.2)
    exact IsSubnormal.step hle' hnorm hih

theorem isSubnormal_inf_centralizer_of_normalizes {N M : Subgroup F} (h : IsSubnormal N M)
    {y : F} (hyN : y ∈ Subgroup.normalizer (N : Set F))
    (hyM : y ∈ Subgroup.normalizer (M : Set F)) :
    IsSubnormal (N ⊓ Subgroup.centralizer ({y} : Set F))
      (M ⊓ Subgroup.centralizer ({y} : Set F)) := by
  have := isSubnormal_inf_conjSub_inf_centralizer h hyM
  rwa [conjSub_eq_of_mem_normalizer hyN, inf_idem] at this

end CFSG.ClassicalInvolution.Q3.Q3T6B
