module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Iso
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Theta
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.SegevSections

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

theorem exists_alpha (h : F5Std a z) (h' : F5Std a' z') :
    ∃ α : G → G', IsIsoOn (Gx a) (Gx a') α := by
  obtain ⟨E, hE⟩ := h.typ.cent_a
  obtain ⟨E', hE'⟩ := h'.typ.cent_a
  obtain ⟨e⟩ := h.iface.nonempty_mulEquiv _ _ E E' hE hE'
  obtain ⟨f, hf, -⟩ := exists_isIsoOn_of_mulEquiv e
  exact ⟨f, hf⟩

theorem segevSection4_of_interface (hI : TwoHSInterface) (hO : AutExtOpen) (hC : CompatOpen)
    (h29 : Segev29) : HNRecog.SegevSection4 := by
  intro G G' _ _ _ _ _ _ a z a' z' ha hL ha' hL'
  have h : F5Std a z := ⟨⟨ha, hL, hI⟩, hO⟩
  have h' : F5Std a' z' := ⟨⟨ha', hL', hI⟩, hO⟩
  obtain ⟨α, hα⟩ := exists_alpha h h'
  obtain ⟨F, hF⟩ := exists_const_fam hC h h' hα
  obtain ⟨θ, hθ⟩ := exists_theta h hF
  exact theta_graphIso hC.cover4A hC.wit20 hC.gen2A h29 h h' hα hθ

end CFSG.EvenSporadicStandard.HNRecog.Section4
