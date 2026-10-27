module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocSimple
public import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.GL32
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.Yardstones.Md0ec50421ce4

theorem hR168 (R : Type) [Group R] (hs : IsSimpleGroup R) (hc : Nat.card R = 168) :
    IsChevSimple 2 R := by
  haveI : Finite R := Nat.finite_of_card_ne_zero (by omega)
  haveI := hs
  have h32 := CFSG.Quasithin.HSRuLoc.Mod.isPSL_three_two_of_simple_card_168 (H := R) hc
  have h27 := CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two h32
  obtain ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.Lie.isLThreeTwo_of_statedClassicalModel h27
  refine Or.inr ⟨TauCeti.CFSGIndex.lie d, ?_, ⟨e⟩⟩
  simp only [ambiguousChev, hd]
  exact Or.inl ⟨hq, trivial⟩

end FR

end CFSG.LocalAnalysis.GLTheoremA
