module

public import CFSG.LieType.SeitzGeneration.OuterSpData
public import CFSG.LieType.SeitzGeneration.SpF2.Main
public import CFSG.LieType.SeitzGeneration.OuterOrthCat
public import CFSG.LieType.SeitzGeneration.OmegaF2.Plus
public import CFSG.LieType.SeitzGeneration.OmegaF2.Minus
public import CFSG.LieType.SeitzGeneration.RootPairOrthOmega
public import CFSG.RankThree.PartOne.SEITZ10.SzMain
public import CFSG.RankThree.PartOne.SEITZ7.SzPairK

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Symplectic


theorem fieldAutData_five_psp {L : Type} [Group L] {n ℓ f : ℕ}
    (hM : StatedClassicalModel L .PSp n ℓ f) : FieldAutData L 5 := by
  obtain ⟨⟨hℓ, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  exact (fieldAutData_projectiveSp_odd (subfieldPairSpOdd subfieldPairSpF2_holds) hn hℓ hf hK
    Nat.prime_five (by norm_num)).of_mulEquiv e Nat.prime_five

end Symplectic

section Orthogonal


theorem fieldAutData_five_pomega {L : Type} [Group L] [Finite L] {t : StatedLieTag} {n ℓ f : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hM : StatedClassicalModel L t n ℓ f) (hℓ : ℓ ≠ 5) : FieldAutData L 5 :=
  fieldAutData_of_model (subfieldPairOmega_of_char2
      (subfieldPairOmegaPlusChar2_of_F2 subfieldPairOmegaPlusF2_holds)
      (subfieldPairOmegaMinusChar2_of_F2 subfieldPairOmegaMinusF2_holds)) ht hM Nat.prime_five (by norm_num) (Ne.symm hℓ)

end Orthogonal

section Suzuki


theorem fieldAutData_five_suzuki {L : Type} [Group L] {ℓ f : ℕ} (hM : CFSG.Blueprint.SuzukiModel L ℓ f)
    (hnS : ¬ IsoLie L (.suzuki 2)) : FieldAutData L 5 := by
  obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := hM
  have hX : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hne : a = 2 → (5 : ℕ) ≠ 5 := by
    rintro rfl
    exact fun _ => hnS (CFSG.RankThree.PartOne.SEITZ7.isoLie_suzuki_of_blueprint ha hX e)
  exact (CFSG.RankThree.PartOne.SEITZ2.fieldAutData_suzuki
    CFSG.RankThree.PartOne.SEITZ10.subfieldPairSz_holds Nat.prime_five le_rfl ha hX
    hne).of_mulEquiv e Nat.prime_five

end Suzuki

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
