module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallJ4

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open

theorem sylowSq_or_sylowCube
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hK : IsSmallStrongP p K) : SylowSq p K ∨ SylowCube p K := by
  rcases hK with hL | hU | hA | ⟨rfl, hL34 | hM⟩ | ⟨rfl, hT | hMcL | hFi⟩ | ⟨rfl, hJ⟩
  · exact Or.inl (sylowSq_of_isSmallLinTwo hp hp2 hL)
  · exact Or.inr (sylowCube_of_isSmallUnitary hp hp2 hU)
  · exact Or.inl (sylowSq_of_isAltTwoP hp hp2 hA)
  · exact Or.inl (sylowSq_of_isLinThreeFour hL34)
  · exact Or.inl (sylowSq_of_isM11 hM)
  · exact Or.inl (sylowSq_of_isTitsGroup hT)
  · exact Or.inr (sylowCube_of_isMcL hs hMcL)
  · exact Or.inl (sylowSq_of_isFi22 hs hFi)
  · exact Or.inr (sylowCube_of_isJ4 hs hJ)

theorem pow_eq_one_of_isSmallStrongP
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hK : IsSmallStrongP p K) (T : Sylow p K)
    (hT : ¬ IsCyclic (T : Subgroup K)) (t : K) (ht : ∃ n : ℕ, t ^ p ^ n = 1) : t ^ p = 1 := by
  rcases sylowSq_or_sylowCube hp hp2 hs hK with hSq | hCube
  · exact pow_eq_one_of_sylowSq hp hSq T hT t ht
  · exact pow_eq_one_of_sylowCube hp hCube T t ht

theorem card_center_of_isSmallStrongP
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hK : IsSmallStrongP p K) (hrk : Open.pRank p (⊤ : Subgroup K) ≤ 2)
    (T : Sylow p K) :
    Nat.card T = p ^ 2 ∨
      (Nat.card T = p ^ 3 ∧ Nat.card (Subgroup.center (T : Subgroup K)) = p) := by
  rcases sylowSq_or_sylowCube hp hp2 hs hK with hSq | hCube
  · exact Or.inl (hSq T)
  · refine Or.inr ⟨(hCube T).1, card_center_of_cube hp T (hCube T).1 ?_⟩
    exact exists_noncomm_of_cube hp hrk T (hCube T).1 (hCube T).2

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
