module

public import CFSG.LargeExtraspecial.S8KB
public import CFSG.LargeExtraspecial.S8A5LF
public import CFSG.LargeExtraspecial.S14Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.LargeExtraspecial.S4

theorem s8_3Stmt_of (hTI : S9.TIPairInput.{0}) (hBadE : S8.Timmesfeld83A5InfLinBadE.{0})
    (hP4 : S9.PGL25ConjResidual.{0}) (hP5 : S9.PGL25TypeIIResidual.{0})
    (hG4 : S8.Timmesfeld83PlusGlobal4.{0}) (hG3 : S8.Timmesfeld83PlusGlobal3.{0})
    (hCorB : S8.TimmesfeldCorBInput) (hFacts : S8.CorBListFacts) (hA5 : S8.CorBListA5Facts)
    (hCE : CentralExtInput.{0}) : S8_3Stmt := by
  intro G _ _ _ S g t hSt hcase
  have hIrr := irr_of_not_isReducible hSt.irr
  rcases hcase with ⟨⟨H, C, ht, ht1, hVQ, hΩ, hd⟩, hnp⟩ | ⟨⟨H, C, ht, ht1, hVQ, hΩ, hd⟩, hp⟩ |
      ⟨⟨H, C, ht, ht1, hVQ, hΩ, hd⟩, hp⟩
  ·
    have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
    obtain ⟨D⟩ := S8.Std.nonempty hCE hNo hΩ
    have hpl := rnPlus_iff_not_isMinus D
    have hdim := D.hdim
    have hmin : D.IsMinus := by
      by_contra h
      exact hnp (hpl.mpr h)
    exact (S8.false_of_A5_of_corB' hTI hBadE hP4 hP5 hCorB hFacts hA5 hCE hIrr hNo hΩ D
      (by omega) hmin hSt.abar_ne).elim
  ·
    have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
    obtain ⟨D⟩ := S8.Std.nonempty hCE hNo hΩ
    have hpl := rnPlus_iff_not_isMinus D
    have hdim := D.hdim
    rcases S8.timmesfeld_8_3_plus hG4 hG3 hCorB hFacts hCE hIrr hNo hΩ D hSt.abar_ne
        (Or.inl ⟨by omega, hpl.mp hp⟩) with h | ⟨-, -, hw⟩ | ⟨h4, -, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨⟨H, C, ht, ht1, hVQ, hΩ, hd⟩, hp, hw⟩)
    · omega
  ·
    have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
    obtain ⟨D⟩ := S8.Std.nonempty hCE hNo hΩ
    have hpl := rnPlus_iff_not_isMinus D
    have hdim := D.hdim
    rcases S8.timmesfeld_8_3_plus hG4 hG3 hCorB hFacts hCE hIrr hNo hΩ D hSt.abar_ne
        (Or.inr ⟨by omega, hpl.mp hp⟩) with h | ⟨h3, -, -⟩ | ⟨-, -, hw⟩
    · exact Or.inl h
    · omega
    · exact Or.inr (Or.inr ⟨⟨H, C, ht, ht1, hVQ, hΩ, hd⟩, hp, hw⟩)

end CFSG.LargeExtraspecial.S14
