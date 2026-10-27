module

public import CFSG.LieType.Chevalley.GraphFixedSimpleComplement

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {τ : Tag}

private theorem prod_map_filter_eq {M ι : Type*} [Monoid M] (p : ι → Prop) [DecidablePred p]
    (f g : ι → M) (hfg : ∀ x, p x → f x = g x) (hg : ∀ x, ¬p x → g x = 1) :
    ∀ l : List ι, ((l.filter p).map f).prod = (l.map g).prod
  | [] => rfl
  | x :: l => by
    by_cases hx : p x
    · rw [List.filter_cons_of_pos (by simpa using hx), List.map_cons, List.prod_cons, hfg x hx,
        List.map_cons, List.prod_cons, prod_map_filter_eq p f g hfg hg l]
    · rw [List.filter_cons_of_neg (by simpa using hx), List.map_cons, List.prod_cons, hg x hx,
        one_mul, prod_map_filter_eq p f g hfg hg l]

section ImageSmul


theorem closed_image_smul (w : WeylGroup τ) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S) :
    ∀ α ∈ (fun β => w • β) '' S, ∀ β ∈ (fun β => w • β) '' S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • α + b • β) → a • α + b • β ∈ (fun β => w • β) '' S := by
  rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ a b ha hb hr
  have e : a • (w • α) + b • (w • β) = w • (a • α + b • β) := by
    rw [smul_add, smul_comm w a α, smul_comm w b β]
  rw [e] at hr ⊢
  exact ⟨a • α + b • β, hS α hα β hβ a b ha hb ((isRoot_smul_iff w).1 hr), rfl⟩

end ImageSmul

section Intersection


theorem rootSpan_inf_rootSpan_le_rootSpan_inter (R : Type) [CommRing R]
    {A B : Set (Fin τ.rank → ℤ)} (hA : ∀ α ∈ A, IsRoot τ α ∧ 0 < height α)
    (hB : ∀ α ∈ B, IsRoot τ α ∧ 0 < height α)
    (hAc : ∀ α ∈ A, ∀ β ∈ A, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ A)
    (hBc : ∀ α ∈ B, ∀ β ∈ B, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ B) :
    rootSpan τ R A ⊓ rootSpan τ R B ≤ rootSpan τ R (A ∩ B) := by
  classical
  intro g hg
  obtain ⟨hgA, hgB⟩ := Subgroup.mem_inf.1 hg
  have hAB : ∀ α ∈ A ∪ B, IsRoot τ α ∧ 0 < height α := fun α hα => hα.elim (hA α) (hB α)
  obtain ⟨l, hl, hm⟩ := exists_list_of_finite
    ((finite_setOf_isRoot τ).subset fun α hα => (hAB α hα).1)
  have key : ∀ {S : Set (Fin τ.rank → ℤ)}, S ⊆ A ∪ B → (∀ α ∈ S, IsRoot τ α ∧ 0 < height α) →
      (∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
        a • α + b • β ∈ S) →
      ∀ {u : (Module.End R (RootModule τ R))ˣ}, u ∈ rootSpan τ R S →
        ∃ c : (Fin τ.rank → ℤ) → R, (∀ α, α ∉ S → c α = 0) ∧
          (l.map fun α => pinnedX τ R α (c α)).prod = u := by
    intro S hS hSpos hSc u hu
    obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq R hSpos hSc (l := l.filter (· ∈ S))
      (hl.filter _) (fun α => by rw [List.mem_filter, hm α]; exact
        ⟨fun h => of_decide_eq_true h.2, fun h => ⟨hS h, decide_eq_true h⟩⟩) hu
    refine ⟨fun α => if α ∈ S then c α else 0, fun α hα => if_neg hα, ?_⟩
    rw [← hc]
    exact (prod_map_filter_eq (· ∈ S) _ _ (fun α hα => by simp only [if_pos hα])
      (fun α hα => by simp only [if_neg hα, pinnedX_zero]) l).symm
  obtain ⟨c, hc0, hc⟩ := key Set.subset_union_left hA hAc hgA
  obtain ⟨d, hd0, hd⟩ := key Set.subset_union_right hB hBc hgB
  have hcd := pinnedX_list_prod_injective l hl (fun α hα => hAB α ((hm α).1 hα)) c d
    (hc.trans hd.symm)
  rw [← hc]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hx
  by_cases hαAB : α ∈ A ∩ B
  · exact Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem hαAB
      (Subgroup.subset_closure ⟨c α, rfl⟩))
  · have hcα : c α = 0 := by
      by_cases hαA : α ∈ A
      · rw [hcd α hα, hd0 α fun h => hαAB ⟨hαA, h⟩]
      · exact hc0 α hαA
    rw [hcα, pinnedX_zero]
    exact one_mem _

theorem rootSpan_inf_rootSpan_image_smul_le (R : Type) [CommRing R] (w : WeylGroup τ)
    {A : Set (Fin τ.rank → ℤ)} (hA : ∀ α ∈ A, IsRoot τ α ∧ 0 < height α)
    (hAc : ∀ α ∈ A, ∀ β ∈ A, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ A)
    (hwA : ∀ α ∈ A, 0 < height (w • α)) :
    rootSpan τ R A ⊓ rootSpan τ R ((fun β => w • β) '' A) ≤
      rootSpan τ R (A ∩ (fun β => w • β) '' A) :=
  rootSpan_inf_rootSpan_le_rootSpan_inter R hA
    (by
      rintro _ ⟨β, hβ, rfl⟩
      exact ⟨IsRoot.smul (hA β hβ).1 w, hwA β hβ⟩)
    hAc (closed_image_smul w hAc)

end Intersection

end CFSG.LieType.Chevalley
