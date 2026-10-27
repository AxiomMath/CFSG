module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSimpleConcl
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParFamily
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParReeF4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSmallA6U33
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTits
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.RankThree.PartOne.K133X.F4

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Fam

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

theorem residualGraph_of_minParResidual
    {Y : Type} [Group Y] [Finite Y]
    (h : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.MinParResidual Y) :
    ResidualGraph Y := by
  intro T hT
  rcases h with he | ⟨d, ⟨q, hq, hdq⟩, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  ·
    obtain ⟨e⟩ := he
    obtain ⟨_, _, _, h0⟩ := twoPar_alt_six
    exact Or.inl (TwoPar.exists_of_equiv e.symm h0 hT)
  ·
    obtain ⟨dd, hv⟩ := d
    simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_three hq
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    rw [hp, hf] at hm
    obtain ⟨e'⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, hm⟩)
    obtain ⟨_, _, _, h0⟩ := twoPar_u33
    exact Or.inl (TwoPar.exists_of_equiv e'.symm h0 hT)
  · obtain ⟨dd, hv⟩ := d
    rcases hd with ⟨m, hm⟩ | ⟨m, hm⟩ | hm
    ·
      simp only at hm
      subst hm
      exact Or.inr (suzuki_cat m hv e hT).2.coatom
    ·
      simp only at hm
      subst hm
      obtain ⟨-, hmodel⟩ := CFSG.RankThree.PartOne.K133X.reeTitsModel_twistedF4_of_isoLie
        (X := Y) (m := m) ⟨hv, ⟨e⟩⟩
      obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e'⟩⟩ :=
        CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hmodel
      have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
      exact Or.inl (TwoPar.exists_of_equiv e'.symm (twoPar_reeF4 ha hK') hT)
    ·
      simp only at hm
      subst hm
      have hmodel := CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := Y) ⟨hv, ⟨e⟩⟩
      obtain ⟨e'⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hmodel
      exact Or.inl (TwoPar.exists_of_equiv e'.symm (twoParLat_tits).toTwoPar hT)

end CFSG.AGLEmbeddingD2.Tits.GN516.Fam
