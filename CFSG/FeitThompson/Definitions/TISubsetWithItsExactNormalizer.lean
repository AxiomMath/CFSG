module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

structure IsTIWithNormalizer (D : Set G) (L : Subgroup G) : Prop where
  nonempty : D.Nonempty
  one_notMem : (1 : G) ∉ D
  normalizer_eq : Subgroup.normalizer D = L
  disjoint_conj_image : ∀ g : G, g ∉ L → Disjoint D (MulAut.conj g '' D)

namespace IsTIWithNormalizer

variable {D : Set G} {L : Subgroup G} (h : IsTIWithNormalizer D L)

include h

theorem subset_compl_singleton_one : D ⊆ ({1} : Set G)ᶜ := by
  intro x hx hx1
  exact h.one_notMem (by simpa [Set.mem_singleton_iff.1 hx1] using hx)

theorem inter_conj_image_eq_empty {g : G} (hg : g ∉ L) : D ∩ MulAut.conj g '' D = ∅ :=
  Set.disjoint_iff_inter_eq_empty.mp (h.disjoint_conj_image g hg)

theorem mem_iff_conj_image_eq {g : G} : g ∈ L ↔ MulAut.conj g '' D = D := by
  rw [← h.normalizer_eq, Subgroup.mem_normalizer_iff_conj_image_eq]

theorem conj_image_eq_of_mem {g : G} (hg : g ∈ L) : MulAut.conj g '' D = D :=
  h.mem_iff_conj_image_eq.1 hg

theorem conj_image_eq_or_disjoint (g : G) :
    MulAut.conj g '' D = D ∨ Disjoint D (MulAut.conj g '' D) := by
  by_cases hg : g ∈ L
  · exact Or.inl (h.conj_image_eq_of_mem hg)
  · exact Or.inr (h.disjoint_conj_image g hg)

theorem disjoint_image_conj_inv {g : G} (hg : g ∉ L) :
    Disjoint D ((fun x => g⁻¹ * x * g) '' D) := by
  have hg' : g⁻¹ ∉ L := fun hc => hg (by simpa using inv_mem hc)
  refine (h.disjoint_conj_image _ hg').mono_right (le_of_eq ?_)
  exact (Set.image_congr' fun x => by simp).symm

theorem disjoint_conj_image_conj_image {g k : G} (hgk : g⁻¹ * k ∉ L) :
    Disjoint (MulAut.conj g '' D) (MulAut.conj k '' D) := by
  have hd := h.disjoint_conj_image _ hgk
  have himg := (Set.disjoint_image_iff (f := (MulAut.conj g : G → G))
    (MulAut.conj g).injective (s := D) (t := MulAut.conj (g⁻¹ * k) '' D)).2 hd
  rw [Set.image_image] at himg
  refine himg.mono_right (le_of_eq ?_)
  refine (Set.image_congr' fun x => ?_).symm
  simp only [MulAut.conj_apply]
  group

theorem not_disjoint_conj_image_iff_mem {g : G} :
    ¬ Disjoint D (MulAut.conj g '' D) ↔ g ∈ L := by
  refine ⟨fun hd => ?_, fun hg hd => ?_⟩
  · by_contra hg
    exact hd (h.disjoint_conj_image g hg)
  · rw [h.conj_image_eq_of_mem hg] at hd
    exact h.nonempty.ne_empty (disjoint_self.mp hd)

theorem normalizer_unique {L' : Subgroup G} (h' : IsTIWithNormalizer D L') : L = L' := by
  rw [← h.normalizer_eq, h'.normalizer_eq]

end IsTIWithNormalizer

theorem isTIWithNormalizer_compl_singleton_one [Nontrivial G] :
    IsTIWithNormalizer (({1} : Set G)ᶜ) ⊤ where
  nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    exact ⟨x, hx⟩
  one_notMem := by simp
  normalizer_eq := by
    refine top_unique fun g _ => ?_
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    simp [Set.mem_compl_iff, Set.mem_singleton_iff, mul_inv_eq_one]
  disjoint_conj_image := by simp

end CFSG.FeitThompson
