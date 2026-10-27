module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Equal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpTheta

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

theorem exists_theta (h : F5Std a z) {F : Fam a α} (hF : ConstOnVertices a F) :
    ∃ θ : G → G', IsTheta a F θ := by
  classical
  refine ⟨fun x => if hx : IsConj a x then F.app (exists_inv_vertex h hx).choose x else 1,
    ⟨fun x hx t ht => ?_⟩⟩
  simp only [dif_pos hx]
  exact hF x hx _ (exists_inv_vertex h hx).choose_spec t ht

end CFSG.EvenSporadicStandard.HNRecog.Section4
