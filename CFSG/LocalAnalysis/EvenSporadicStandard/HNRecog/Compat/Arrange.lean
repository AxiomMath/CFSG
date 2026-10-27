module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpArr4B

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

@[expose] def Arranged (a : G) (F : Fam a α) : Prop :=
  ∀ x ∈ orb3A a a ∪ orb4B a a, ∀ t ∈ InvIn (Gxy a x), ∀ t' ∈ InvIn (Gxy a x),
    F.app t x = F.app t' x

theorem exists_arranged (hC : Cover4A) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) :
    ∃ F : Fam a α, Arranged a F := by
  have hαa : α a = a' := iso_apply_self h h' hα
  obtain ⟨F₀⟩ := exists_fam h h' (IsConj.refl a) (β := α) (by rw [hαa]) (by rw [hαa]; exact hα)
  obtain ⟨F₁, h₁⟩ := cp_arrange_3A h h' hα F₀
  obtain ⟨F₂, h₂, h₃⟩ := cp_arrange_4B hC h h' hα F₁ h₁
  refine ⟨F₂, fun x hx => ?_⟩
  rcases hx with hx | hx
  · exact h₂ x hx
  · exact h₃ x hx

end CFSG.EvenSporadicStandard.HNRecog.Section4
