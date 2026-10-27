module

public import CFSG.Quasithin.MS93.ASC132
public import CFSG.GH74.QTGen4.DCopy.Quasithin.MS93.SkConcl
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.MS93.ASBlocksHat
public import CFSG.Quasithin.MS93.ASHyp
public import CFSG.Quasithin.MS93.ASSL3

public section

namespace CFSG.Quasithin.MS93

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem asC132_of_ms93_of_simple_F4
    (hS : RankTwoLieSimple) (hms : MS93AS_F4) :
    ASInputs.AS_C_1_32_F4 := by
  intro G _ _ G₀ R L hMS hL hG
  have h := puHyp_of_msPair_of_simple hS hMS hL hG
  rcases hms G G₀ R L h with h2 | h3 | h4 | ⟨-, h5⟩ | h6 | h8 | h10 | ⟨-, h11⟩ | ⟨-, h13⟩
  · exact Or.inr (Or.inl (isAltBlockType_of_case2 h h2))
  · rcases hMS.2.1 with ha | hb
    · exact Or.inr (Or.inr (Or.inl (isSp4Block_of_case3 h h3 (isOddRadical_of_msPair h.le ha))))
    · exact absurd h3 (not_case3_of_g2Two h hb.2.2.1)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isModO2Surj_of_case4 h h4))))
  · obtain ⟨n, F, _, _, α, hF, hmod, -⟩ := isModO2Surj_of_case5 h h5
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, F, inferInstance, inferInstance, α, hF, hmod⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (isHatA6Block_of_case6 h h6))))
  · obtain ⟨α, hmod, -⟩ := isModO2Surj_of_case8 h h8
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, α,
      by rw [ZMod.card, pow_one], hmod⟩)))
  · exact Or.inl (isG2Block_of_case10 h h10)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isModO2Surj_of_case11 h h11))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isModO2Surj_of_case13 h h13))))

theorem asC132_of_ms93_F4
    (hms : MS93AS_F4) :
    ASInputs.AS_C_1_32_F4 :=
  asC132_of_ms93_of_simple_F4 rankTwoLieSimple_holds hms

end CFSG.Quasithin.MS93
