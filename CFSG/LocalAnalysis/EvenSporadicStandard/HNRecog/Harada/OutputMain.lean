module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.OutputQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.OutputInputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

theorem harada_half_of_inputs (hS : Setting25Exists) (h27 : Lemma27Exists)
    (hA : GoldschmidtTheoremA) : HaradaHalf := by
  intro G _ _ _ hK t ht E hE
  obtain ⟨z, z₁, ι, zv, R0, F, h, hzt, htz, hCz, hF⟩ := hS G hK t ht E hE
  obtain ⟨φ, hs⟩ := h27 G hK h hzt htz hCz
  exact ⟨z, orderOf_eq_prime (by simpa [pow_two] using h.z_sq) h.z_ne_one,
    isExtraspecialPlusByA5WrTwo_of_lemma_2_10 h hA hzt htz hs hF⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
