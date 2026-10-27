module

public import CFSG.LieType.Chevalley.StandardParabolicCells
public import CFSG.LieType.Chevalley.ReducedWordBorel

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem wordProd_mem_parabolicWeylGroup
    {J : Set (Fin τ.rank)} {ω : List (Fin τ.rank)}
    (h : ∀ i ∈ ω, i ∈ J) : (coxeterSystem τ).wordProd ω ∈ parabolicWeylGroup τ J := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil]; exact one_mem _
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons]
    exact mul_mem (Subgroup.subset_closure ⟨i, h i List.mem_cons_self, rfl⟩)
      (ih fun j hj => h j (List.mem_cons_of_mem i hj))

theorem eq_parabolicSubgroup_of_borelGroup_le
    {A : Subgroup (ModGL τ K)}
    (hB : borelGroup τ K ≤ A) (hA : A ≤ adjointGroup τ K) :
    A = parabolicSubgroup τ K {i | weylElt τ K i 1 ∈ A} := by
  refine le_antisymm (fun g hg => ?_) (sup_le hB ((Subgroup.closure_le _).2 ?_))
  · have hg' : g ∈ ⋃ w, bruhatCell τ K w := by
      rw [← adjointGroup_eq_iUnion_bruhatCell]
      exact hA hg
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
    have hn : canonicalRep (coxeterSystem τ) K w ∈ A := by
      have := mul_mem (mul_mem (inv_mem (hB hb)) hg) (inv_mem (hB hb'))
      simpa [mul_assoc] using this
    obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
    have hconj : (borelGroup τ K).map (MulAut.conj
        (canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω))).toMonoidHom ≤ A := by
      rintro _ ⟨x, hx, rfl⟩
      exact mul_mem (mul_mem hn (hB hx)) (inv_mem hn)
    have hletters := reduced_word_borel_extraction τ K A hB ω hω hconj
    have hwJ := wordProd_mem_parabolicWeylGroup (J := {i | weylElt τ K i 1 ∈ A}) hletters
    exact bruhatCell_subset_parabolicSubgroup hwJ hw
  · rintro _ ⟨i, hi, rfl⟩
    exact hi

theorem borel_overgroup_classification
    (τ : Tag) (K : Type) [Field K] :
    (∀ A : Subgroup (ModGL τ K), borelGroup τ K ≤ A → A ≤ adjointGroup τ K →
      A = parabolicSubgroup τ K {i | weylElt τ K i 1 ∈ A}) ∧
    ∀ A : Subgroup (ModGL τ K), borelGroup τ K ≤ A → A ≤ adjointGroup τ K →
      ∃! J : Set (Fin τ.rank), A = parabolicSubgroup τ K J := by
  refine ⟨fun A hB hA => eq_parabolicSubgroup_of_borelGroup_le hB hA, fun A hB hA =>
    ⟨_, eq_parabolicSubgroup_of_borelGroup_le hB hA, fun J hJ => ?_⟩⟩
  ext i
  rw [Set.mem_ofPred_eq, hJ, weylElt_mem_parabolicSubgroup_iff]

end CFSG.LieType.Chevalley
