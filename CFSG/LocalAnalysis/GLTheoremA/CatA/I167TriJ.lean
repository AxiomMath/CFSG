module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriJLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

set_option linter.unusedSectionVars false



theorem exists_label_of_type167 {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X)
    (h : Type167Grp 3 (X ⧸ Subgroup.center X)) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧ Type167Canon (canonLabel lab) := by
  rcases h with ⟨-, n, -, hn, h⟩ | ⟨-, n, -, hn, h⟩ | ⟨n, k, hodd, hn3, hk1, hk, -, h⟩
  · obtain ⟨lab, hl, ht, hr⟩ := exists_label_isLnA hq hn h
    exact ⟨lab, hl, Or.inl ⟨ht, by omega⟩⟩
  · obtain ⟨lab, hl, ht, hr⟩ := exists_label_isOmMA hq hn h
    exact ⟨lab, hl, Or.inr (Or.inl ⟨ht, by omega⟩)⟩
  · obtain ⟨lab, hl, hc⟩ := exists_label_isOmPA hq hodd hn3 hk hk1 h
    rcases hc with hc | hc
    · exact ⟨lab, hl, Or.inl hc⟩
    · exact ⟨lab, hl, Or.inr (Or.inr hc)⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end
