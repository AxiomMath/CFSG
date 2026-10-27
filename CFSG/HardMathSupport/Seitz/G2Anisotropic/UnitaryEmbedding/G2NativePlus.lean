module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.G2Family
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.G2PlusCore
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.G2OddQPlusFive
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxDone
public import CFSG.Goldschmidt.Final

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator


theorem g2NativePlaneGenPlus_proved : G2NativePlaneGenPlus := by
  intro K _ _ hK p hp hp5 hpq E₁ hE hcard
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := ringChar.of_eq h2
    have hev := CFSG.RankThree.Chevalley.EvenG2.even_card_of_charTwo (K := K)
    have hK4 : 4 ≤ Nat.card K := by
      obtain ⟨m, hm⟩ := hev
      omega
    exact g2_plane_cenGen_eq_top_even (RankThree.PartOne.SEITZ6.maxSL2SL2G2_of_top
        CFSG.Goldschmidt.topStatement) K
      hK4 hp hp5 hpq E₁ hE.2 hcard
  · have : Fintype K := Fintype.ofFinite K
    obtain ⟨p', hcp, n, hp', hcard'⟩ := FiniteField.card' (K := K)
    have hpeq : p' = ringChar K := CharP.eq K hcp (ringChar.charP K)
    have hp2 : p' ≠ 2 := fun h => h2 (hpeq ▸ h)
    have hpo : Odd p' := hp'.eq_two_or_odd'.resolve_left hp2
    have hodd : Odd (Nat.card K) := by
      rw [Nat.card_eq_fintype_card, hcard']
      exact hpo.pow
    have h5 : 5 ≤ Nat.card K := by
      obtain ⟨m, hm⟩ := hodd
      by_contra hlt
      have h3 : Nat.card K = 3 := by omega
      have : p ∣ 4 := by rw [h3] at hpq; exact hpq
      have := Nat.le_of_dvd (by norm_num) this
      omega
    exact closure_cenGen_adjointG2_odd_qplus_eq_top_of_five K hodd h5 hp hp5 hpq E₁ hE.2 hcard

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
