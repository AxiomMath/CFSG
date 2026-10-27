module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeG2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.AGLEmbedding.ParabHub

theorem exists_sylow_of_isSylowTwoOf_top {Y : Type} [Group Y] [Finite Y] {T : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) : ∃ T' : Sylow 2 Y, (T' : Subgroup Y) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
  exact ⟨hT.2.1.toSylow hidx, rfl⟩

section Catalog


theorem threeDvd_lieIndex {Y : Type} [Group Y] [Finite Y] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2Index d.1) (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q => exact threeDvd_sl r q hd hv e T J hNJ hJ
  | twistedA r q =>
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    change q.p = 2 at hd
    rw [hd] at h
    exact threeDvd_of_model_psu h T J hNJ hJ
  | B r q =>
    change q.p = 2 at hd
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at h
      exact threeDvd_of_model_psp h T J hNJ hJ
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
        (by omega) e
      rw [hd] at h
      exact threeDvd_of_model_psp h T J hNJ hJ
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    exact threeDvd_of_model_pomegaPlus h T J hNJ hJ
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact threeDvd_of_model_pomegaMinus h T J hNJ hJ
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    exact threeDvd_g2 (e.trans b.symm) T J hNJ hJ
  | _ => exact hd.elim

end Catalog

section Main


theorem kFactParabolicThree : KFactParabolicThree := by
  intro Y _ _ hY T J hT hNJ hJ
  obtain ⟨T', rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  rcases hY with ⟨d, hd, ⟨e⟩⟩ | h2 | h3
  · exact threeDvd_lieIndex d hd e T' J hNJ hJ
  · exact threeDvd_small (Or.inl h2) _ J hT hNJ hJ
  · exact threeDvd_small (Or.inr h3) _ J hT hNJ hJ

end Main

end CFSG.AGLEmbedding
