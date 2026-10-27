module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeTypes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInvFam
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInvSmall
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree

public section

namespace CFSG.AGLEmbedding.ParabHub.ParabThreeInv

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over CFSG.QuasithinUnique.L246C127
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

theorem invOver_alt
    {S : Type} [Group S] {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (e : S ≃* alternatingGroup (Fin n)) : InvOver S := by
  rcases hn with rfl | rfl | rfl
  · exact InvOver.of_mulEquiv e.symm invOver_alt_five
  · exact InvOver.of_mulEquiv e.symm invOver_alt_six
  · exact InvOver.of_mulEquiv e.symm invOver_alt_eight

theorem invOver_model_seven
    {S : Type} [Group S]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 2 7 1) : InvOver S := by
  obtain ⟨e⟩ := nonempty_equiv_sl_three_two_of_model_seven h
  exact InvOver.of_mulEquiv (e.trans Vol2Native.A312L.Seven.z8Equiv).symm invOver_z8

theorem invOver_lieModel_psu_three_three
    {K : Type} [Group K] (h : CFSG.Blueprint.LieModel K .PSU 3 3 1) : InvOver K := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel h
  exact InvOver.of_mulEquiv e.symm invOver_u33

theorem invOver_catalog_seven
    {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq : q.card = 7) (hd : d.1 = .A 1 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : InvOver Y := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
  have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  rw [hp, hf] at h
  exact invOver_model_seven h

theorem invOver_catalog_psu_three_three
    {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hq : q.card = 3) (hd : d.1 = .twistedA 2 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : InvOver Y := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hp, hf] at h
  exact invOver_lieModel_psu_three_three (Or.inl ⟨by decide, h⟩)


theorem invThree_lieIndex {Y : Type} [Group Y] [Finite Y] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2Index d.1) (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : InvThree J := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q => exact invThree_sl r q hd hv e T J hNJ hJ
  | twistedA r q =>
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    change q.p = 2 at hd
    rw [hd] at h
    exact invThree_of_model_psu h T J hNJ hJ
  | B r q =>
    change q.p = 2 at hd
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at h
      exact invThree_of_model_psp h T J hNJ hJ
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
        (by omega) e
      rw [hd] at h
      exact invThree_of_model_psp h T J hNJ hJ
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    exact invThree_of_model_pomegaPlus h T J hNJ hJ
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact invThree_of_model_pomegaMinus h T J hNJ hJ
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    exact invThree_g2 (e.trans b.symm) T J hNJ hJ
  | _ => exact hd.elim

end CFSG.AGLEmbedding.ParabHub.ParabThreeInv

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.ParabHub.ParabThreeInv


theorem kFactParabolicThreeInv_holds : KFactParabolicThreeInv := by
  intro Y _ _ hY T J hT hNJ hJ
  obtain ⟨T', rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  rcases hY with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩, ⟨e⟩⟩
  · exact invThree_lieIndex d hd e T' J hNJ hJ
  · exact invOver_alt hn e _ J hT hNJ hJ
  · exact invOver_catalog_seven hq hd e _ J hT hNJ hJ
  · exact invOver_catalog_psu_three_three hq hd e _ J hT hNJ hJ

end CFSG.AGLEmbedding
