module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2EndN
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2G5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246DoubleMain

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

structure S2Inputs : Prop where
  lemma246Inputs : Lemma246Inputs
  a39 : Vol2Native.A39ForSQTKCat
  list : Vol2Native.Lemma2_3_9_7_listedW

theorem lemma2_4_s2_of_inputs
    (c : S2Inputs) : Lemma2_4_s2 := by
  intro G _ _ T M H S L D n hcfg
  obtain ⟨t, M₀, x₀, q, W, B⟩ := hcfg.exists_base
  have h246 : Lemma246Double := L246Double.lemma246DoubleLin2_proved c.lemma246Inputs
  obtain ⟨y, D₁, D₂, O⟩ := B.exists_ok h246
  by_cases hle : T ⊓ Subgroup.normalizer (thompsonJ S : Set G) ≤ M₀
  · exact O.false_of_M₀_eq_T (O.M₀_eq_T hle) c.a39 c.list listedLin2OddRank
  · exact O.base.false_of_lt_normT h246 O.hT₁ O.hT₂ O.hD O.hC O.hDx O.thompsonJ_M₀
      O.ncard_maxElemAbelian_R hle

end CFSG.QuasithinUnique.Lin2
