module

public import CFSG.Quasithin.Background.CharTwoLocal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Glauberman281

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type*} [Group G]

theorem charTwo_of_le {W M : Subgroup G} (hWM : W ≤ M) (hM : CharTwo M)
    (hO : pCoreOf 2 M ≤ pCoreOf 2 W) : CharTwo W := by
  intro g hg
  have hgC : g ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    Subgroup.centralizer_le (fun x hx => hO hx) hg.2
  exact hO (hM ⟨hWM hg.1, hgC⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC.Glauberman281
