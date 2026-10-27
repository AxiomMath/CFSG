module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.A5WrTwoFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]

theorem AschbacherHyp.le_commutator [Finite C] (hC : AschbacherHyp C Q) : Q ≤ commutator C := by
  have hE : IsExtraspecialPGroup 2 Q := hC.plus.isExtraspecialPGroup
  haveI : Finite Q := hC.plus.finite
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE
  let W : Subgroup C := Q ⊓ commutator C
  have hZW : centerOf Q ≤ W := by
    refine le_inf inf_le_left ?_
    intro z hz
    have hzQ : z ∈ Q := (mem_inf.mp (show z ∈ Q ⊓ centralizer (Q : Set C) from hz)).1
    have hzc : (⟨z, hzQ⟩ : Q) ∈ Subgroup.center Q := (mem_centerOf_iff ⟨z, hzQ⟩).1 hz
    have hmem : (⟨z, hzQ⟩ : Q) ∈ _root_.commutator Q := by
      rw [hE.2.1]
      exact hzc
    have hmap : z ∈ (_root_.commutator Q).map Q.subtype := ⟨⟨z, hzQ⟩, hmem, rfl⟩
    rw [Subgroup.map_subtype_commutator] at hmap
    exact Subgroup.commutator_mono le_top le_top hmap
  have hinv : ∀ g ∈ commutator C, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hg w hw
    exact ⟨(inferInstance : Q.Normal).conj_mem w hw.1 g,
      mul_mem (mul_mem hg hw.2) ((commutator C).inv_mem hg)⟩
  rcases hC.irreducible W hZW inf_le_left hinv with hW | hW
  ·
    exfalso
    have hcomm : commutator C ≤ Q := by
      refine le_of_forall_commutator_mem_centerOf hE hC.centralizer_le (K := commutator C) ?_
      intro g hg x hx
      have hmem : ⁅g, x⁆ ∈ W := by
        refine ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          exact mul_mem ((inferInstance : Q.Normal).conj_mem x hx g) (Q.inv_mem hx)
        · rw [_root_.commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x)
      rw [hW] at hmem
      exact hmem
    have hab_q : ∀ x y : C ⧸ Q, x * y = y * x := by
      intro x y
      obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective Q x
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective Q y
      rw [← commutatorElement_eq_one_iff_mul_comm]
      rw [← map_commutatorElement (f := QuotientGroup.mk' Q) (g₁ := x') (g₂ := y')]
      exact (QuotientGroup.eq_one_iff _).mpr (hcomm (by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x') (Subgroup.mem_top y')))
    obtain ⟨a, b, hab⟩ := A5WrTwo.exists_mul_ne_mul
    obtain ⟨e⟩ := hC.quotient
    apply hab
    calc a * b = e (e.symm a) * e (e.symm b) := by simp
      _ = e (e.symm a * e.symm b) := by rw [map_mul]
      _ = e (e.symm b * e.symm a) := by rw [hab_q (e.symm a) (e.symm b)]
      _ = e (e.symm b) * e (e.symm a) := by rw [map_mul]
      _ = b * a := by simp
  · exact inf_eq_left.mp hW

end CFSG.EvenSporadicStandard.HNRecog
