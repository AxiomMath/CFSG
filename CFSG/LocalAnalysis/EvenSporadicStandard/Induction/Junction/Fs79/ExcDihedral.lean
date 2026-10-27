module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.GorensteinWalter

theorem hasDihedralSylowTwo_of_excType {X : Type} [Group X] [Finite X] (h : ExcType X) :
    HasDihedralSylowTwo (X ⧸ center X) := by
  rcases h with h | ⟨p, f, hp, hp2, hmodel⟩
  · obtain ⟨e⟩ := h
    exact hasDihedralSylowTwo_of_mulEquiv e hasDihedralSylowTwo_alternatingGroupSeven
  · rcases hmodel with ⟨-, hmodel⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
    · obtain ⟨hadm, K, hK, hKf, hcard, ⟨e⟩⟩ := hmodel
      let := hK
      have : Finite K := hKf
      have hodd : IsOddPrimePower (Nat.card K) :=
        ⟨p, f, hp, hp.odd_of_ne_two hp2, hadm.2.1, hcard⟩
      let e' : (X ⧸ center X) ≃* PSL2 K :=
        e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
      have : Finite (PSL2 K) := Finite.of_equiv _ e'.toEquiv
      exact hasDihedralSylowTwo_of_mulEquiv e' (psl2_odd_hasDihedralSylowTwo_model K hodd)
    all_goals exact absurd hn (by decide)

end CFSG.EvenSporadicStandard.Induction.Junction
