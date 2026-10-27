module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Const5

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

@[expose] def ConstOnVertices (a : G) (F : Fam a α) : Prop :=
  ∀ x, IsConj a x → ∀ t ∈ InvIn (Gxy a x), ∀ t' ∈ InvIn (Gxy a x), F.app t x = F.app t' x

theorem fam_const (hC : CompatOpen) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (F : Fam a α) (hF : Arranged a F) : ConstOnVertices a F := by
  intro x hx t ht t' ht'
  have hmem : x ∈ gammaSet a z a := h.loc.gamma.self.eq_gamma a x (IsConj.refl a) hx
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff] at hmem
  rcases hmem with
    (((((((hxa | hx2A) | hx2B) | hx3A) | hx4A) | hx4B) | hx5A) | hx5E) | hx6A
  · rw [hxa] at ht ht' ⊢
    exact const_self F ht ht'
  · exact const_2A_2B h F (Or.inl hx2A) ht ht'
  · exact const_2A_2B h F (Or.inr hx2B) ht ht'
  · exact hF x (Or.inl hx3A) t ht t' ht'
  · exact const_4A hC.cover4A hC.wit4A h h' hα F hF hx4A ht ht'
  · exact hF x (Or.inr hx4B) t ht t' ht'
  · exact const_5A hC.gen5A h h' hα F hF hx5A ht ht'
  · exact const_5E hC.cover4A hC.wit4A hC.wit5e h h' hα F hF hx5E ht ht'
  · exact const_6A h F hF hx6A ht ht'

theorem exists_const_fam (hC : CompatOpen) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) : ∃ F : Fam a α, ConstOnVertices a F := by
  obtain ⟨F, hF⟩ := exists_arranged hC.cover4A h h' hα
  exact ⟨F, fam_const hC h h' hα F hF⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
