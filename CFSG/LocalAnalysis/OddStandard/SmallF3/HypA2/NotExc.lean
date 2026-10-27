module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.ClassS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.SympField
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Phase2Inputs
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.StandardRecognition

theorem not_evenStandardException_of_inSA (hG2 : G2DerivedU33) {X : Type} [Group X]
    (h : InSA X) (hnotA : ¬ ∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) :
    ¬ Recognition.Exact.EvenStandardException X := by
  unfold InSA at h
  obtain ⟨-, h20, hodd, hL34, hHe, -, -⟩ := h
  rintro (h1 | h2 | h3 | ⟨K4, _, _, hK4, he4⟩ | ⟨K5, _, _, hK5, he5⟩ | h6 | h7 | h8)
  ·
    have hcard : Nat.card X = 60 := by
      rw [GH74.card_of_lieModel_PSL (G := X) (n := 2) (p := 2) (f := 2) (by norm_num) h1]
      decide
    omega
  ·
    have hcard : Nat.card X = 168 := by
      rw [GH74.card_of_lieModel_PSL (G := X) (n := 3) (p := 2) (f := 1) (by norm_num) h2]
      decide
    omega
  ·
    have hM : Models.LieModel X .PSL 4 2 1 :=
      modelsLieModel_of_statedClassicalModel
        (statedClassicalModel_of_blueprintLieModel
          (by decide) h3)
    exact hnotA ⟨8, by norm_num,
      nonempty_mulEquiv_alternating_eight_of_lieModel
        X hM⟩
  ·
    exact hnotA ⟨6, by norm_num,
      nonempty_mulEquiv_alternating_six_of_symplectic_field K4 hK4 he4⟩
  ·
    have hcard : Nat.card K5 = 2 := by rw [Nat.card_eq_fintype_card]; exact hK5
    have hLie : Blueprint.LieModel
        ↥⁅Chevalley.adjointGroup .G2 K5, Chevalley.adjointGroup .G2 K5⁆ .PSU 3 3 1 :=
      hG2 K5 hcard
    obtain ⟨e⟩ := he5
    have hX : Blueprint.LieModel X .PSU 3 3 1 := Blueprint.LieModel.of_mulEquiv e.symm hLie
    exact (hodd 3 Nat.prime_three (by norm_num)) ⟨.PSU, 3, 1, hX⟩
  ·
    have hPSp : Models.LieModel X .PSp 2 3 1 :=
      lieModel_PSp_two_three_of_lieModel_PSU_four_two
        X (modelsLieModel_of_statedClassicalModel
          (statedClassicalModel_of_blueprintLieModel
            (by decide) h6))
    have hB : Blueprint.LieModel X .PSp 2 3 1 :=
      blueprintLieModel_of_statedClassicalModel
        (by decide)
        (statedClassicalModel_of_modelsLieModel
          (by decide) hPSp)
    exact (hodd 3 Nat.prime_three (by norm_num)) ⟨.PSp, 2, 1, hB⟩
  · exact hL34 h7
  · exact hHe h8

end CFSG.OddStandard.SmallF3.HypA2
