module

public import CFSG.CGT.T75P.Syl
public import CFSG.CGT.T75P.Split81
public import CFSG.CGT.T75P.Inputs

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank

theorem step81_of_odd (h214 : Lemma214) (hInv : InvolutionClassInput) (hIso : Section3IsoInput)
    (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (h66 : Sec66) (hOdd : Odd81)
    (hR : A8SylowInput) : Step81 := by
  intro G _ T T₁ hy hq hT hnat
  have hc := sec6Ctx_of_natural h214 hInv hIso hy hq hT hnat
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  obtain ⟨hTH, hHN, hHnorm⟩ := hSub_data T T₁
  have hodd := hOdd G T T₁ hy hq hT hnat
  have hindex := odd_index_of_odd_relIndex hy.pair.wc hTH hHN hHnorm hnat hodd
  have hsplit := exists_complement_hSub81 h1 h62 h63 h66 hc hnat
  rcases hR G hy.nonab T (hSub T (normIn T₁ T)) hTH hy.pair.wc hnat hsplit hindex with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨8, by norm_num, by norm_num, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨9, by norm_num, by norm_num, h⟩)))

theorem step82_of_odd (hOdd : Odd82) (hR : M24SylowInput) : Step82 := by
  intro G _ T T₁ hy hq hT hnat
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  obtain ⟨hTH, hHN, hHnorm⟩ := hSub_data T T₁
  have hodd := hOdd G T T₁ hy hq hT hnat
  have hindex := odd_index_of_odd_relIndex hy.pair.wc hTH hHN hHnorm hnat hodd
  rcases hR G hy.nonab T (hSub T (normIn T₁ T)) hTH hy.pair.wc hnat hindex with h | h
  · exact Or.inl ⟨5, 1, by norm_num, by norm_num, h⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

end CFSG.CGT.T75P
