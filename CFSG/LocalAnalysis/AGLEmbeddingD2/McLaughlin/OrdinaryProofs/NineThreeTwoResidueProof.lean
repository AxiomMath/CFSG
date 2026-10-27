module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.NineThreeTwoResidue
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LargeFieldProof
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.ComponentClassification.TBLit

theorem isClassicalOrG2IndexTwo_of_lieField_eq_two {i : TauCeti.LieTypeIndex}
    (hi : IsClassicalOrG2Index i) (h : LieField i = 2) : IsClassicalOrG2IndexTwo i := by
  cases i <;> simp only [IsClassicalOrG2Index, IsClassicalOrG2IndexTwo, LieField] at hi h ⊢ <;>
    exact h

section LargeFieldCertificates


theorem nineThreeTwoResidue_proved : NineThreeTwoResidue := by
  intro G _ _ M S L hL h2 hSyl hsolv hQ _hZ
  obtain ⟨d, hd, h2d, ⟨e⟩⟩ := hQ
  have hlt := lieField_lt_four_of_nineThreeTwo largeFieldParabolic_proved hL h2 hSyl hsolv d hd e
  exact absurd (isClassicalOrG2IndexTwo_of_lieField_eq_two hd
    (lieField_eq_two_of_lt_four d hd hlt)) h2d

end LargeFieldCertificates

section GriessCertificates


theorem kFactBlockCentreNine_proved : KFactBlockCentreNine :=
  kFactBlockCentreNine_of_residue griessMultipliersAllModels_holds nineThreeTwoResidue_proved

end GriessCertificates

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

end
