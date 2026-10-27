module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PrimeDefs
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Split

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem insp443List'_of_for' (h : For' QTKSimpleList) : Insp443List' := by
  intro G _ _ T M L B Tp VB K hS hU hO hKB hNK hq hKM hVK hLK hcen hList
  exact h G T M L B Tp VB K
    ⟨hS, hU, hO, hKB, hNK, hq, hKM, hVK, hLK, hcen⟩ hList

theorem insp443List'_of_items (h1 : For' ItemAlt) (h2 : For' ItemOdd) (h3 : For' ItemChar2)
    (h4 : For' ItemChar2Rank3) (h5 : For' ItemSporadic) : Insp443List' := by
  refine insp443List'_of_for' ?_
  have h : For' (fun S _ => ItemAlt S ∨ ItemOdd S ∨ ItemChar2 S ∨ ItemChar2Rank3 S ∨
      ItemSporadic S) := For'.or h1 (For'.or h2 (For'.or h3 (For'.or h4 h5)))
  exact For'.mono (fun S _ hS => (qtkSimpleList_iff S).mpr hS) h

end CFSG.SectionRank.QTK.Insp443

end
