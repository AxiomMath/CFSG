module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

theorem pRank_centralizer_le_two_of_isSylowOf {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) {D : Subgroup Y} {x : Y} (hD : Nat.card D = p ^ 2)
    (hS : CFSG.ABGLocalTools.IsSylowOf p D (centralizer ({x} : Set Y))) :
    CFSG.Open.pRank p (centralizer ({x} : Set Y)) ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEC, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (centralizer ({x} : Set Y))
  have h1 : p ^ CFSG.Open.pRank p (centralizer ({x} : Set Y)) ∣
      Nat.card (centralizer ({x} : Set Y)) := hcard ▸ Subgroup.card_dvd_of_le hEC
  have h2 := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h1
  have h3 := hS.card_eq
  rw [hD] at h3
  have h4 : (Nat.card (centralizer ({x} : Set Y))).factorization p = 2 :=
    (Nat.pow_right_injective hp.two_le h3).symm
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
