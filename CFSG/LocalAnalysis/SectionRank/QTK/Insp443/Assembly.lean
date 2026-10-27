module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Families
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Split

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem for_itemAlt_of
    (h8 : For (fun S _ => Nonempty (S ≃* alternatingGroup (Fin 8))))
    (h9 : For (fun S _ => Nonempty (S ≃* alternatingGroup (Fin 9)))) : For ItemAlt := by
  intro G _ _ T M L B Tp VB K hHyp hP
  obtain ⟨n, hn5, hn9, he⟩ := hP
  rcases le_or_gt n 7 with hn7 | hn8
  · exact for_alt_le_seven G T M L B Tp VB K hHyp ⟨n, hn5, hn7, he⟩
  · have hn : n = 8 ∨ n = 9 := by omega
    rcases hn with rfl | rfl
    · exact h8 G T M L B Tp VB K hHyp he
    · exact h9 G T M L B Tp VB K hHyp he

theorem for_itemOdd_of
    (hSp4 : For (fun S _ => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ StatedClassicalModel S .PSp 2 p 1))
    (hG2 : For (fun S _ => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ChevalleyExceptionalModel S .G2 p 1))
    (hL4 : For (fun S _ => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∃ a : ℕ, p = 2 ^ a + 1) ∧
      StatedClassicalModel S .PSL 4 p 1))
    (hU4 : For (fun S _ => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∃ b : ℕ, p + 1 = 2 ^ b) ∧
      StatedClassicalModel S .PSU 4 p 1)) : For ItemOdd := by
  intro G _ _ T M L B Tp VB K hHyp hP
  obtain ⟨p, hp, hp2, hL2 | hL3 | hSp4' | hG2' | hL4' | hU4'⟩ := hP
  · exact for_odd_twoRank_two G T M L B Tp VB K hHyp ⟨p, hp, hp2, Or.inl hL2⟩
  · exact for_odd_twoRank_two G T M L B Tp VB K hHyp ⟨p, hp, hp2, Or.inr hL3⟩
  · exact hSp4 G T M L B Tp VB K hHyp ⟨p, hp, hp2, hSp4'⟩
  · exact hG2 G T M L B Tp VB K hHyp ⟨p, hp, hp2, hG2'⟩
  · exact hL4 G T M L B Tp VB K hHyp ⟨p, hp, hp2, hL4'⟩
  · exact hU4 G T M L B Tp VB K hHyp ⟨p, hp, hp2, hU4'⟩

theorem for_itemChar2_of
    (hL3 : For (fun S _ => ∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f))
    (hSp4 : For (fun S _ => ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f))
    (hU4 : For (fun S _ => ∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel S .PSU 4 2 f))
    (hG2 : For (fun S _ => ∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f))
    (hD4 : For (fun S _ => ∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f))
    (hF4 : For (fun S _ => ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f))
    (hU5 : For (fun S _ => StatedClassicalModel S .PSU 5 2 2))
    (hTits : For (fun S _ => ReeTitsModel S .Tits 2 1)) : For ItemChar2 := by
  intro G _ _ T M L B Tp VB K hHyp hP
  rcases hP with
    ⟨f, hL2 | hL3' | hU3 | hSp4' | hU4' | hG2' | hD4' | hF4' | hSz⟩ | hU5' | hTits'
  · exact for_bender G T M L B Tp VB K hHyp ⟨f, Or.inl hL2⟩
  · exact hL3 G T M L B Tp VB K hHyp ⟨f, hL3'⟩
  · exact for_bender G T M L B Tp VB K hHyp ⟨f, Or.inr (Or.inl hU3)⟩
  · exact hSp4 G T M L B Tp VB K hHyp ⟨f, hSp4'⟩
  · exact hU4 G T M L B Tp VB K hHyp ⟨f, hU4'⟩
  · exact hG2 G T M L B Tp VB K hHyp ⟨f, hG2'⟩
  · exact hD4 G T M L B Tp VB K hHyp ⟨f, hD4'⟩
  · exact hF4 G T M L B Tp VB K hHyp ⟨f, hF4'⟩
  · exact for_bender G T M L B Tp VB K hHyp ⟨f, Or.inr (Or.inr hSz)⟩
  · exact hU5 G T M L B Tp VB K hHyp hU5'
  · exact hTits G T M L B Tp VB K hHyp hTits'

end CFSG.SectionRank.QTK.Insp443
