module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
import CFSG.GH74.Orders.LieType
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusTools
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.Quasithin.Background.F918V3T3C
import CFSG.Sporadic.Presentation.McLExact
import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.AGLEmbedding

namespace ThreeEightFive

theorem card_sporadic_McL :
    Nat.card (TauCeti.CFSGIndex.sporadic .McL).Group = 898128000 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  exact (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.McL.card_McL

theorem card_sporadic_J4 :
    Nat.card (TauCeti.CFSGIndex.sporadic .J4).Group = 86775571046077562880 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  exact (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.J4.card_J4

end ThreeEightFive


namespace ThreeEightFive

private theorem three_dvd_card_alternatingGroup_six :
    3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

private theorem five_dvd_card_alternatingGroup_ten :
    5 ∣ Nat.card (alternatingGroup (Fin 10)) := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

private theorem prime_dvd_card_catGroup_linTwo {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 2 ≤ n) {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d) :
    p ∣ Nat.card (CatGroup d) := by
  rw [card_catGroup_linTwo (p := p) (n := n) hp2 (by omega) hd]
  exact (dvd_pow_self p (by omega)).trans (dvd_mul_right _ _)

private theorem prime_dvd_card_catGroup_unitary {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) : p ∣ Nat.card (CatGroup d) := by
  have h := pow_dvd_card_catGroup_unitary hd
  obtain ⟨r, -, hdr⟩ := hd
  have hfe : d.1.fieldExponent = r.exponent := by
    rw [hdr]
    exact TauCeti.LieTypeIndex.fieldExponent_twistedA 2 r
  rw [hfe] at h
  exact (dvd_pow_self p (by have := r.exponent_pos; omega)).trans h

private theorem three_dvd_card_catGroup_ree {m : ℕ}
    {hv : (TauCeti.LieTypeIndex.reeG2 m).Valid} :
    3 ∣ Nat.card (CatGroup ⟨.reeG2 m, hv⟩) := by
  have h := CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m
      (S := CatGroup ⟨.reeG2 m, hv⟩) ⟨hv, ⟨MulEquiv.refl _⟩⟩)
  obtain ⟨-, -, -, -, hcard⟩ := h
  rw [hcard]
  have hq : 3 ∣ 3 ^ (2 * m + 1) := dvd_pow_self 3 (by omega)
  have hX : 3 ∣ (3 ^ (2 * m + 1)) ^ 3 := hq.trans (dvd_pow_self _ (by norm_num))
  unfold CFSG.Open.ordRee
  refine hX.trans ?_
  exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)

private theorem three_dvd_card_catGroup_linTwo_eight {r : TauCeti.PrimePower}
    (hr : r.p = 2) (he : r.exponent = 3) {hv : (TauCeti.LieTypeIndex.A 1 r).Valid} :
    3 ∣ Nat.card (CatGroup ⟨.A 1 r, hv⟩) := by
  have hL := CFSG.Models.lieModel_A 1 r hv (MulEquiv.refl _)
  rw [hr, he] at hL
  rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num)
    (CFSG.Models.LieModel.toBlueprint (by decide) hL)]
  decide

private theorem three_dvd_card_catGroup_linThree_four {r : TauCeti.PrimePower}
    (hr : r.p = 2) (he : r.exponent = 2) {hv : (TauCeti.LieTypeIndex.A 2 r).Valid} :
    3 ∣ Nat.card (CatGroup ⟨.A 2 r, hv⟩) := by
  have hL := CFSG.Models.lieModel_A 2 r hv (MulEquiv.refl _)
  rw [hr, he] at hL
  rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num)
    (CFSG.Models.LieModel.toBlueprint (by decide) hL)]
  decide

private theorem five_dvd_card_catGroup_suzuki_two
    {hv : (TauCeti.LieTypeIndex.suzuki 2).Valid} :
    5 ∣ Nat.card (CatGroup ⟨.suzuki 2, hv⟩) := by
  obtain ⟨a, -, hcard⟩ :=
    CFSG.RankThree.PartTwo.Sec6.BThreeCensus.card_eq_suzukiOrder
      (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index 2 hv)
  rw [hcard]
  exact CFSG.RankThree.PartTwo.Sec6.BThreeCensus.five_dvd_suzukiOrder a

private theorem five_dvd_card_catGroup_tits {hv : TauCeti.LieTypeIndex.tits.Valid} :
    5 ∣ Nat.card (CatGroup ⟨.tits, hv⟩) := by
  rw [CFSG.AGLEmbedding.KFactProofs.SmallIdent.card_of_isTitsGroup
    (⟨⟨.tits, hv⟩, rfl, ⟨MulEquiv.refl _⟩⟩ :
      CFSG.AGLEmbedding.IsTitsGroup (CatGroup ⟨.tits, hv⟩))]
  norm_num

private theorem three_dvd_card_sporadic_M11 : 3 ∣ Nat.card TauCeti.SporadicName.M11.Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  rw [← Nat.card_congr e.toEquiv]
  exact CFSG.Quasithin.F918V3T3.three_dvd_card_M11

private theorem five_dvd_card_sporadic_McL :
    5 ∣ Nat.card (TauCeti.CFSGIndex.sporadic .McL).Group := by
  rw [card_sporadic_McL]
  norm_num

private theorem eleven_dvd_card_sporadic_J4 :
    11 ∣ Nat.card (TauCeti.CFSGIndex.sporadic .J4).Group := by
  rw [card_sporadic_J4]
  norm_num

end ThreeEightFive

theorem prime_dvd_card_of_isNineFourIndex {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {i : TauCeti.CFSGIndex} (hi : CFSG.LocalAnalysis.RankThreeTheoremC.IsNineFourIndex q i) :
    q ∣ Nat.card i.Group := by
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating n _ =>
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ThreeEightFive.three_dvd_card_alternatingGroup_six
    · exact ThreeEightFive.five_dvd_card_alternatingGroup_ten
  | sporadic s =>
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ThreeEightFive.three_dvd_card_sporadic_M11
    · exact ThreeEightFive.five_dvd_card_sporadic_McL
    · exact ThreeEightFive.eleven_dvd_card_sporadic_J4
  | lie d =>
    rcases hi with ⟨r, hrp, hr2, hrd⟩ | ⟨r, hrp, hrd⟩ | ⟨rfl, m, hm⟩ |
      ⟨rfl, ⟨r, hr2, hr3, hrd⟩ | ⟨r, hr2, hr2', hrd⟩⟩ | ⟨rfl, hd | hd⟩
    · haveI : Fact r.p.Prime := ⟨r.prime_p⟩
      have hp2 : r.p ≠ 2 := by rw [hrp]; exact hq2
      rw [← hrp]
      exact ThreeEightFive.prime_dvd_card_catGroup_linTwo (p := r.p) (n := r.exponent)
        hp2 hr2 ⟨r, hrd, rfl, rfl⟩
    · rw [← hrp]
      exact ThreeEightFive.prime_dvd_card_catGroup_unitary (p := r.p) ⟨r, rfl, hrd⟩
    · obtain ⟨d1, hv⟩ := d
      change d1 = .reeG2 m at hm
      subst d1
      exact ThreeEightFive.three_dvd_card_catGroup_ree
    · obtain ⟨d1, hv⟩ := d
      change d1 = .A 1 r at hrd
      subst d1
      exact ThreeEightFive.three_dvd_card_catGroup_linTwo_eight hr2 hr3
    · obtain ⟨d1, hv⟩ := d
      change d1 = .A 2 r at hrd
      subst d1
      exact ThreeEightFive.three_dvd_card_catGroup_linThree_four hr2 hr2'
    · obtain ⟨d1, hv⟩ := d
      change d1 = .suzuki 2 at hd
      subst d1
      exact ThreeEightFive.five_dvd_card_catGroup_suzuki_two
    · obtain ⟨d1, hv⟩ := d
      change d1 = .tits at hd
      subst d1
      exact ThreeEightFive.five_dvd_card_catGroup_tits

theorem prime_dvd_card_of_nineFourListGroup {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Y : Type}
    [Group Y] (h : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q Y) :
    q ∣ Nat.card Y := by
  obtain ⟨-, i, hi, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact prime_dvd_card_of_isNineFourIndex hq hq2 hi

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
