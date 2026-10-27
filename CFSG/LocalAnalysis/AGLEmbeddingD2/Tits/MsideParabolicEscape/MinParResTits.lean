module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTits
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParResSz
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSmallA6U33

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin
  CFSG.Open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

set_option linter.unusedSectionVars false

section Tits


theorem kFact_of_tits {Y : Type} [Group Y] [Finite Y] {L R P : Subgroup Y}
    (hR : R ≤ Subgroup.normalizer (L : Set Y)) (hR2 : IsPGroup 2 R)
    (hS : IsSylowTwoOf (R ⊓ L) L) (hP : IsMinOverBorel L (R ⊓ L) P)
    (hv : TauCeti.LieTypeIndex.tits.Valid)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.tits, hv⟩).Group) :
    KFactConcl L R P := by
  have hmodel := CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := ↥L ⧸ Subgroup.center ↥L)
    ⟨hv, ⟨e⟩⟩
  obtain ⟨e'⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hmodel
  exact kFact_of_twoPar_cat hR hR2 hS hP e'
    ⟨_, _, _, (twoParLat_tits).toTwoPar⟩

end Tits

section Small


theorem kFact_of_alt_six {Y : Type} [Group Y] [Finite Y] {L R P : Subgroup Y}
    (hR : R ≤ Subgroup.normalizer (L : Set Y)) (hR2 : IsPGroup 2 R)
    (hS : IsSylowTwoOf (R ⊓ L) L) (hP : IsMinOverBorel L (R ⊓ L) P)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(alternatingGroup (Fin 6))) : KFactConcl L R P :=
  kFact_of_twoPar_cat hR hR2 hS hP e twoPar_alt_six

theorem kFact_of_u33 {Y : Type} [Group Y] [Finite Y] {L R P : Subgroup Y}
    (hR : R ≤ Subgroup.normalizer (L : Set Y)) (hR2 : IsPGroup 2 R)
    (hS : IsSylowTwoOf (R ⊓ L) L) (hP : IsMinOverBorel L (R ⊓ L) P)
    (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower) (hq : q.card = 3)
    (hdq : d.1 = .twistedA 2 q)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group) : KFactConcl L R P := by
  obtain ⟨dd, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_three hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hp, hf] at h
  obtain ⟨e'⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
  exact kFact_of_twoPar_cat hR hR2 hS hP e' twoPar_u33

end Small

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
