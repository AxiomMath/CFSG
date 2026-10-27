module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167FieldDict
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint


theorem exc_omPA_type_det {G : Type} [Group G] {n k : ℕ} (hn3 : 3 ≤ n) (hk : 1 ≤ k)
    (hnk : k = 1 → 5 ≤ n) (h : catalogIs G (isOmPA n (2 ^ k))) {t : StatedLieTag} {ν g : ℕ}
    (hm : CFSG.Blueprint.LieModel G t ν 2 g) :
    g = k ∧ ((4 ≤ n ∧ t = .POmegaPlus ∧ ν = n) ∨ (n = 3 ∧ 2 ≤ k ∧ t = .PSL ∧ ν = 4)) := by
  rcases fld_lieModel_of_isOmPA hk hn3 hnk h with ⟨hn4, hm'⟩ | ⟨rfl, hk2, hm'⟩
  · obtain ⟨ht, hν, hg⟩ :=
      CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique (s := .POmegaPlus) (m := n) (f := k)
        (Or.inl rfl) hm' hm
    exact ⟨hg, Or.inl ⟨hn4, ht, hν⟩⟩
  · obtain ⟨ht, hν, hg⟩ :=
      CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (m := 4) (f := k) (by norm_num) hm' hm
    exact ⟨hg, Or.inr ⟨rfl, hk2, ht, hν⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end
