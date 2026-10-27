module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCore
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthHigh

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem card_zmod3_eq_three_pow_one' : Nat.card (ZMod 3) = 3 ^ 1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]
  norm_num

theorem isQuasisimple_omegaGroup_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) : CFSG.IsQuasisimple (omegaGroup hQ) := by
  have hQ' : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  obtain ⟨hq, -⟩ := CFSG.ComponentClassification.CatLeafProof.X10Lin.centralModel_orthogonal_derived
    (p := 3) (e := 1) (n := 3) Nat.prime_three (by norm_num) le_rfl
    card_zmod3_eq_three_pow_one' Q hQ' (Or.inl ⟨hdim, le_rfl⟩)
  rw [omegaGroup_eq_commutator hQ (by omega)]
  exact hq

theorem isQuasisimple_omegaGroup_of_five_le_seven (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) (h7 : Module.finrank (ZMod 3) V ≤ 7) :
    CFSG.IsQuasisimple (omegaGroup hQ) := by
  have hcases : Module.finrank (ZMod 3) V = 5 ∨ Module.finrank (ZMod 3) V = 6 ∨
      Module.finrank (ZMod 3) V = 7 := by omega
  rcases hcases with h | h | h
  · exact isQuasisimple_omegaGroup_five hQ h
  · rcases Int.units_eq_one_or (quadSign Q) with hs | hs
    · exact isQuasisimple_omegaGroup_six_plus hQ h hs
    · exact isQuasisimple_omegaGroup_six_minus hQ h hs
  · exact isQuasisimple_omegaGroup_seven hQ h

end CFSG.OddStandard.SmallF3.Omega
