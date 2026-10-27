module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_glaIsBmax {p : ℕ} (hp : p.Prime) {B F U : Subgroup G} (hBmax : GLAIsBmax p B)
    (hF : IsElemAbelian p F) (hFU : F ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥)
    (hUp : IsPGroup 2 U) : Nat.card F ≤ Nat.card B := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian hp hF
  have hk : m ≤ CFSG.Open.pRank p (Subgroup.normalizer (U : Set G)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hFU hF hm
  have hN : CFSG.Open.pRank p (Subgroup.normalizer (U : Set G)) ≤ GLATwoLocalRank p G := by
    unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank
    exact le_csSup (bddAbove_twoLocalPRanks hp.one_lt) ⟨_, ⟨U, hU, hUp, rfl⟩, rfl⟩
  have hB : Nat.card B = p ^ GLATwoLocalRank p G := hBmax.2.1
  rw [hm, hB]
  exact Nat.pow_le_pow_right hp.pos (le_trans hk hN)

theorem twoLocalRank_le_of_glaIsBmax {p : ℕ} (hp : p.Prime) {X B : Subgroup G}
    (hBmax : GLAIsBmax p B) : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hB : IsElemAbelian p B := hBmax.1
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian hp hB
  have hBm : m ≤ CFSG.Open.pRank p B := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB hm
  refine le_trans ?_ hBm
  unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank
  refine csSup_le' ?_
  rintro k ⟨H, ⟨P, hP1, hP2, rfl⟩, rfl⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E hEH hE
  have hPG1 : P.map X.subtype ≠ ⊥ := fun h =>
    hP1 ((Subgroup.map_eq_bot_iff_of_injective P X.subtype_injective).1 h)
  have hPG2 : IsPGroup 2 (P.map X.subtype) := hP2.map X.subtype
  have hle := Subgroup.le_normalizer_map (H := P) X.subtype
  have hE' : IsElemAbelian p (E.map X.subtype) := CFSG.SectionRank.isElemAbelian_map hE X.subtype
  have hcard : Nat.card ↥(E.map X.subtype) = Nat.card ↥E :=
    Subgroup.card_map_of_injective X.subtype_injective
  have hEN : E.map X.subtype ≤ Subgroup.normalizer ((P.map X.subtype : Subgroup G) : Set G) :=
    (Subgroup.map_mono hEH).trans hle
  have hb := card_le_of_glaIsBmax hp hBmax hE' hEN hPG1 hPG2
  rw [hcard, hm] at hb
  exact hb

end CFSG.LocalAnalysis.GLTheoremA.I114
