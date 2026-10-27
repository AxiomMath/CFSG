module

public import CFSG.GH74.E2.Cases
public import CFSG.GH74.E2.CaseIG
public import CFSG.GH74.E2.CaseIIG
public import CFSG.GH74.RouteRefine

public section

namespace CFSG.GH74.E2

theorem s_restrictedEvenThin_of_cases (h5 : NoOddRankFive) (hI : NoCaseI) (hII : NoCaseII) :
    S_restrictedEvenThin := by
  intro G _ _ hs hnonab hrank hgen hK hnab hLx hre
  by_contra hcon
  have hH : Hyp G := ⟨hs, hnonab, hrank, hgen, hK, hnab, hLx, hre⟩
  have h3 : 3 ≤ Assembly.evenRank G := by omega
  obtain ⟨p, A, R, hp, hp2, hA, hAcard, hR, hR2, hnorm⟩ := exists_rank_three_of_evenRank h3
  rcases lemma24 hgen hp hp2 hA hAcard hR hR2 hnorm with
    ⟨h5', t, ht, B, hBC, hBab, hBcard⟩ | ⟨rfl, t, hc⟩ | ⟨rfl, t, t', a, B, hc⟩
  · have h1 := h5 G hH t ht p hp h5' B hBC hBab
    have h2 : p < p ^ 2 := by
      calc p = p * 1 := (mul_one p).symm
        _ < p * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
        _ = p ^ 2 := (sq p).symm
    omega
  · exact hI G hH t A hc
  · exact hII G hH t t' a A B hc

theorem s_restrictedEvenThin_of_leaves (hCl2 : Cl2Statement) (h5 : NoOddRankFive)
    (hI : NoCaseI) (hII : NoCaseIIComp) : S_restrictedEvenThin :=
  s_restrictedEvenThin_of_cases h5 hI (noCaseII_of hCl2 hII)

theorem s_restrictedEvenThin_of_leaves' (hCl2 : Cl2Statement) (hComp : ComponentList)
    (hD : K0Data) (hI : NoCaseI) (hII : NoCaseIIComp) : S_restrictedEvenThin :=
  s_restrictedEvenThin_of_leaves hCl2 (noOddRankFive_of hComp hD) hI hII

theorem s_restrictedEvenThin_of_data (hCl2 : Cl2Statement) (hComp : ComponentList)
    (hD : K0Data) (hD3 : K0Data3) (hQ8 : Q8Lemma) (hI : NoCaseIQ8) (hII : NoCaseIIComp) :
    S_restrictedEvenThin :=
  s_restrictedEvenThin_of_leaves hCl2 (noOddRankFive_of hComp hD)
    (noCaseI_of hComp hD hD3 hQ8 hI) hII

theorem s_restrictedEvenThin_of_local (hCl2 : Cl2Statement) (hComp : ComponentList)
    (hD : K0Data) (hD3 : K0Data3) (hQ8 : Q8Lemma) (hI : NoCaseIQ8) (hα : NoCaseIIAlpha)
    (hβ : NoCaseIIBeta) : S_restrictedEvenThin :=
  s_restrictedEvenThin_of_data hCl2 hComp hD hD3 hQ8 hI (noCaseIIComp_of hComp hD hD3 hQ8 hα hβ)

end CFSG.GH74.E2
