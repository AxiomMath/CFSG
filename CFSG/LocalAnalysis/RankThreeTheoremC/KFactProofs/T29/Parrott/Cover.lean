module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverTorusRank
public import CFSG.LocalAnalysis.AGLEmbedding.CoverRankLift
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus
public import CFSG.RankThree.PartOne.N143.SectionListLie

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti
open CFSG.LocalAnalysis.RankThreeTheoremC (IsLinThreeCover3)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.AGLEmbedding.KFactProofs.CoverThree (CoverE6RankFour card_center_linThree)
open CFSG.RankThree.PartTwo.Sec4.Census (tableOrder card_center_dvd_tableOrder
  lieModel_of_namesTag tripleCoverLie_of_griess)

section Tables

theorem tableOrder_E6_dvd (p f : ℕ) : tableOrder .E6 0 p f ∣ 3 := by
  unfold tableOrder
  have h1 : CFSG.Blueprint.Multiplier.genericOrders .E6 0 p f = (Nat.gcd 3 (p ^ f - 1), 1) := by
    simp [CFSG.Blueprint.Multiplier.genericOrders]
  have h2 : CFSG.Blueprint.Multiplier.exceptionalOrders .E6 0 p f = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rw [h1, h2]
  simpa using Nat.gcd_dvd_left 3 (p ^ f - 1)

theorem tableOrder_twistedE6_dvd (p f : ℕ) : tableOrder .twistedE6 0 p f ∣ 12 := by
  unfold tableOrder
  have h1 : CFSG.Blueprint.Multiplier.genericOrders .twistedE6 0 p f =
      (Nat.gcd 3 (p ^ f + 1), 1) := by
    simp [CFSG.Blueprint.Multiplier.genericOrders]
  have h2 : (CFSG.Blueprint.Multiplier.exceptionalOrders .twistedE6 0 p f).1 *
      (CFSG.Blueprint.Multiplier.exceptionalOrders .twistedE6 0 p f).2 ∣ 4 := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rw [h1]
  have h3 : Nat.gcd 3 (p ^ f + 1) ∣ 3 := Nat.gcd_dvd_left _ _
  have := mul_dvd_mul (mul_dvd_mul h3 (dvd_refl 1)) h2
  simpa using this

end Tables

section Cover

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem false_of_four_le_pRank (h : T29Setup X L x)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L)) : False := by
  have := pRank_component_le h
  omega

theorem false_of_elemAbelian_four (h : T29Setup X L x) {B : Subgroup ↥L}
    (hBp : ∀ b ∈ B, b ^ 3 = 1) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBcard : 3 ^ 4 ≤ Nat.card B) : False :=
  false_of_four_le_pRank h (CFSG.AGLEmbedding.le_pRank_of_pow_le_card Nat.prime_three le_top
    ⟨⟨⟨fun a b => Subtype.ext (hBc a a.2 b b.2)⟩⟩, hBp⟩ hBcard)

theorem p_eq_three_of_card_eq_three {q : PrimePower} (hq : q.card = 3) : q.p = 3 :=
  (CFSG.RankThree.PartOne.N143.primePower_eq_three hq).1

theorem isLinThreeCover3_of_center_ne_bot (hGA : GriessMultipliersAllModels)
    (hE6 : CoverE6RankFour) (h : T29Setup X L x) (hZ : center ↥L ≠ ⊥) {m : ValidLieTypeIndex}
    (hch : m.1.characteristic ≠ 3) (e : (↥L ⧸ center ↥L) ≃* (CFSGIndex.lie m).Group) :
    IsLinThreeCover3 m ∧ Nat.card (center ↥L) = 3 := by
  have hq : CFSG.Open.IsQuasisimple ↥L := h.comp.2.2
  have hq' : CFSG.IsQuasisimple ↥L :=
    CFSG.AGLEmbedding.KFactProofs.CoverFive.isQuasisimple_of_open hq
  have hZp : IsPGroup 3 (center ↥L) := h.center_isPGroup
  have h3Z : 3 ∣ Nat.card (center ↥L) :=
    CFSG.AGLEmbedding.KFactProofs.CoverFive.dvd_card_center_of_isPGroup Nat.prime_three hZ hZp
  have hodd : Odd (Nat.card (center ↥L)) :=
    CFSG.AGLEmbedding.KFactProofs.CoverFive.odd_card_center_of_isPGroup Nat.prime_three
      (by norm_num) hZp
  have htc := tripleCoverLie_of_griess hGA m ↥L ⟨hq', h3Z, ⟨e⟩⟩
  suffices hd : IsLinThreeCover3 m from ⟨hd, card_center_linThree hGA hq hZp hZ hd e⟩
  obtain ⟨dd, hv⟩ := m
  cases dd with
  | A r q =>
    obtain ⟨hpn, hpq⟩ := htc
    by_cases hr : r + 1 = 3
    · obtain rfl : r = 2 := by omega
      exact Or.inl ⟨q, rfl, hpq⟩
    · exfalso
      have hmod := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
      obtain ⟨B, hBp, hBc, hBcard⟩ :=
        CFSG.AGLEmbedding.KFactProofs.CoverFive.exists_elemAbelian_four_psl_of_ne_two
          Nat.prime_three (by norm_num) (by omega) h3Z hodd hmod hpn
          (by simpa only [PrimePower.card_def] using hpq)
      exact false_of_elemAbelian_four h hBp hBc hBcard
  | twistedA r q =>
    rcases htc with ⟨hpn, hpq⟩ | ⟨-, hq3⟩
    · by_cases hr : r + 1 = 3
      · obtain rfl : r = 2 := by omega
        exact Or.inr ⟨q, rfl, hpq⟩
      · exfalso
        have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
        obtain ⟨B, hBp, hBc, hBcard⟩ :=
          CFSG.AGLEmbedding.KFactProofs.CoverFive.exists_elemAbelian_four_psu_of_ne_two
            Nat.prime_three (by norm_num) (by omega) h3Z hodd hmod hpn
            (by simpa only [PrimePower.card_def] using hpq)
        exact false_of_elemAbelian_four h hBp hBc hBcard
    · exact absurd (p_eq_three_of_card_eq_three hq3)
        (by simpa [LieTypeIndex.characteristic_twistedA] using hch)
  | B r q =>
    exact absurd (p_eq_three_of_card_eq_three htc.2)
      (by simpa [LieTypeIndex.characteristic_B] using hch)
  | G2 q =>
    exact absurd (p_eq_three_of_card_eq_three htc)
      (by simpa [LieTypeIndex.characteristic_G2] using hch)
  | E6 q =>
    exfalso
    have hm := lieModel_of_namesTag (t := .E6) ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    have hc3 : Nat.card (center ↥L) = 3 :=
      CFSG.AGLEmbedding.KFactProofs.CoverThree.card_center_eq_three_of_dvd hZp hZ (m := 3)
        ((card_center_dvd_tableOrder hGA hq' e hm).trans (tableOrder_E6_dvd q.p q.exponent))
        (by norm_num)
    have hZc : IsCyclic (center ↥L) := isCyclic_of_prime_card (p := 3) hc3
    exact false_of_four_le_pRank h (hE6 ↥L hq hZ hZp hZc ⟨.E6 q, hv⟩ htc ⟨e⟩)
  | twistedE6 q =>
    exfalso
    have hm := lieModel_of_namesTag (t := .twistedE6) ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    have hc3 : Nat.card (center ↥L) = 3 :=
      CFSG.AGLEmbedding.KFactProofs.CoverThree.card_center_eq_three_of_dvd hZp hZ (m := 12)
        ((card_center_dvd_tableOrder hGA hq' e hm).trans
          (tableOrder_twistedE6_dvd q.p q.exponent)) (by norm_num)
    have hZc : IsCyclic (center ↥L) := isCyclic_of_prime_card (p := 3) hc3
    exact false_of_four_le_pRank h (hE6 ↥L hq hZ hZp hZc ⟨.twistedE6 q, hv⟩ htc ⟨e⟩)
  | C r q => exact htc.elim
  | D r q => exact htc.elim
  | twistedD r q => exact htc.elim
  | E7 q => exact htc.elim
  | E8 q => exact htc.elim
  | F4 q => exact htc.elim
  | trialityD4 q => exact htc.elim
  | suzuki k => exact htc.elim
  | reeG2 k => exact htc.elim
  | reeF4 k => exact htc.elim
  | tits => exact htc.elim

end Cover

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
