module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltOrbits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamOrbitsLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11Orbits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTitsOrbits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UPrimeExcL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallJ4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcL

public section

namespace CFSG.AGLEmbedding

open KFactProofs.SmallIdent KFactProofs.UPrimeExcL34

theorem five_le_of_isSmallLinTwo {p : ℕ} {K : Type} [Group K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : IsSmallLinTwo p K) : 5 ≤ p := by
  obtain ⟨d, hd, -⟩ := hK
  have h9 := card_ne_nine_of_isLinTwoIndex hd
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  by_contra hlt
  have : p = 3 ∨ p = 4 := by omega
  rcases this with rfl | rfl
  · exact h9 (by norm_num)
  · exact absurd hp (by norm_num)

theorem kFactSmallOrbits_of_smallIdent
    (h : KFactSmallIdent) : KFactSmallOrbits := by
  intro K _ _ hs hnab hc p hp hp2 T hT hΓ hAut hFi hTc
  rcases isSmallStrongP_of_autRank h hs hnab hc hp hp2 T hT hΓ hAut with
    hK | hK | hK | ⟨rfl, hK | hK⟩ | ⟨rfl, hK | hK | hK⟩ | ⟨rfl, hK⟩
  · exact Or.inr (Or.inl ⟨hK, five_le_of_isSmallLinTwo hp hp2 hK,
      orbits_of_isSmallLinTwo hp hp2 hK T⟩)
  · exfalso
    have h3 := (sylowCube_of_isSmallUnitary hp hp2 hK T).1
    rw [hTc] at h3
    have := hp.one_lt
    have h4 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right this (by norm_num)
    omega
  · exact Or.inr (Or.inr ⟨hK, orbits_of_isAltTwoP hp hp2 hK T⟩)
  · exact Or.inl (orbits_of_orbitTrans hTc (fun x hx hx1 y hy hy1 =>
      (localData_of_isLinThreeFour hK T).trans x hx hx1 y hy hy1))
  · exact Or.inl (orbits_of_orbitTrans hTc (orbitTrans_m11 hK T))
  · exact Or.inl (orbits_of_isTitsGroup hs hnab hK T)
  · exfalso
    have h3 := (sylowCube_of_isMcL hs hK T).1
    rw [hTc] at h3
    omega
  · exact absurd ⟨rfl, hK⟩ hFi
  · exfalso
    have h3 := (sylowCube_of_isJ4 hs hK T).1
    rw [hTc] at h3
    omega

end CFSG.AGLEmbedding
