module

public import CFSG.CGT.A8S.Assembly
public import CFSG.CGT.A8S.Top
public import CFSG.CGT.T75P.Inputs

public section

namespace CFSG.CGT.A8S

theorem a8SylowInput_of_parts (hHoltA9 : HoltA9Statement) (hCore : CoreStatementA8)
    (hPair : PairStatementA8) (hN0 : N0StatementA8) (hL2 : N0StatementA8 → L2StatementA8)
    (hR3 : R3StatementA8) (hR5 : R5StatementA8) : CFSG.CGT.T75P.A8SylowInput := by
  intro G _ _ _ hna T H hTH hwc hnat hcompl hodd
  have h : A8Hyp T H := ⟨hTH, hwc, hnat, hcompl, hodd⟩
  rcases hCore G hna T H h with hC | hA9
  · obtain ⟨T₁, hyp⟩ := hPair G hna T H h hC
    obtain ⟨X, hNX, -, φ, hφ⟩ := jankoA8CtxInput_of_parts hN0 hL2 hR3 hR5 G T T₁ hyp
    rcases eq_top_or_nonempty_mulEquiv_alt9 hHoltA9 h hNX φ hφ with htop | hA9
    · exact Or.inl ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans φ⟩
    · exact Or.inr hA9
  · exact Or.inr hA9

end CFSG.CGT.A8S
