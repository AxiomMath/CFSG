module

public import CFSG.GF2Type.Smith1979W3.T1216PGLHand
public import CFSG.GF2Type.Smith1979W3.T1216PGLModel
public import CFSG.GF2Type.Smith1979W3.T1216PGLSquare
public import CFSG.GF2Type.Smith1979W3.T1216NoA8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 CFSG.GF2Type.Smith1979W3.Cert690

theorem t1216W3NoPGL27_of (hP : CensusPlusProp) (hF : PGLFactsProp) (hPS : PGLSquareProp) :
    T1216W3NoPGL27 := by
  intro G _ _ _ S hw hirr hb h336
  obtain ⟨L, hL, hK⟩ := exists_mbarModel_eq_KPGL hP hF S hw hirr hb h336
  have hL' : ∀ v, qPlus (L v) = S.q v := hL
  have hSigma := pgl_square_cases S hF hPS hL' hK
  have hSigma2 := pgl_exists_moved S hF hPS hL' hK
  simp only [← ρ_mem_pglM0_iff S L] at hSigma hSigma2
  exact false_of_pglData S hw (pglM0 S L) (pglM0_le S L) (relIndex_pglM0 S L hF hK)
    (pgl_exists_conj S L hF hK) (pgl_centralizer_outer S L hF hK)
    (pgl_centralizer_inner S L hF hK) (pgl_eq_z_of_commute S L hF hw h336 hL hK)
    hSigma hSigma2

theorem t1216WidthThree_of_cert690 (hP : CensusPlusProp) (hM : CensusMinusProp)
    (hF : PGLFactsProp) (hPS : PGLSquareProp) (hA8 : A8SquareProp) : T1216WidthThree :=
  t1216WidthThree_of (t1216W3Census_of hP hM hF) (t1216W3NoPGL27_of hP hF hPS)
    (t1216W3NoA8_of hP hF hA8) t1216W3Minus

end CFSG.GF2Type.Smith1979W3

end
