module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Lang.AnisoE6.ClGen
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Lang.AnisoE6 TauCeti
  CFSG.TauCetiBridge CFSG.RankThree.PartOne.KE CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar (sylowTorus_of_blocks_of_three_lt not_dvd_of_blocks
  not_dvd_div_of_720)

section Classes

theorem sylowTorus_cat_E8_three {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp : p.Prime) (h7 : 7 ≤ p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 3) : SylowTorus (Cat ⟨.E8 q, hv⟩) p 4 := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at he
  have hS : SylowTorus (adjointGroup Tag.E8 K) p ([3, 3, 3, 3].count 3) :=
    sylowTorus_of_blocks_of_three_lt 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E8 e8ThreeWord) [3, 3, 3, 3] e8Three_charpoly e8Three_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
  exact (show SylowTorus (adjointGroup Tag.E8 K) p 4 from hS).of_mulEquiv e.symm

theorem sylowTorus_cat_E8_six {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp : p.Prime) (h7 : 7 ≤ p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 6) : SylowTorus (Cat ⟨.E8 q, hv⟩) p 4 := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at he
  have hS : SylowTorus (adjointGroup Tag.E8 K) p ([6, 6, 6, 6].count 6) :=
    sylowTorus_of_blocks_of_three_lt 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E8 e8SixWord) [6, 6, 6, 6] e8Six_charpoly e8Six_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
  exact (show SylowTorus (adjointGroup Tag.E8 K) p 4 from hS).of_mulEquiv e.symm

end Classes

end CFSG.LieType.SeitzGeneration.ExcHigh
