module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2B3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2B2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Statements

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2

theorem lemma2_4_25_B (hC54 : LemmaC54_3_s2) (h567 : Lemma245_C56_7)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hP1 : CompChi0Block)
    (hP2 : NoProperA5Block) : Lemma2_4_25_B := by
  intro G _ _ T M H S L cfg x hxT hxN hxU hA
  obtain ⟨t, h⟩ := exists_data cfg
  have c := ctx_of hC54 h567 h
  obtain ⟨P₂, hE, hI⟩ := c.exists_P₂
  exact
    { hA with
      Ux_inf := c.Ux_inf hE hI hxN hA.x_phi hxU
      LSI_gamma := c.LSI_gamma
      star := fun H₁ hc hLSI hφ hex => c.star hE hI h37 h39 hP1 hP2 H₁ hc hLSI hφ hex }

end CFSG.QuasithinUnique.A5
