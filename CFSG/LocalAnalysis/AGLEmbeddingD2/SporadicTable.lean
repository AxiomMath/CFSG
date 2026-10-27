module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.DatumSup
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.RankThree.PartOne.TCB.Sporadic
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
public import CFSG.RankThree.PartOne.KP.Co3Aut
public import CFSG.RankThree.PartOne.KP.SporadicRankFi22
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.RankThree.PartOne.SPOR.OuterB
public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import CFSG.Sporadic.Schreier.Fi24Schreier
public import CFSG.Sporadic.Schreier.PairHSOut
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Sporadic.Schreier.PairMcLOut
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.SuzOddCore.Outer

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

theorem d2IndexDatum_of_not_sq_dvd {L : Type*} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hOut : Nat.card (Outer L) ≤ 2) (h : ¬ p ^ 2 ∣ Nat.card L) :
    D2IndexDatum L p := by
  refine ⟨fun hdvd => ?_, Or.inl h⟩
  have : Finite (MulAut L) := MulEquiv.finite_left
  have h1 := Nat.le_of_dvd Nat.card_pos hdvd
  have h2 := hp.two_le
  omega

@[expose] def d2SporadicOrder : TauCeti.SporadicName → ℕ
  | .M11 => 2 ^ 4 * 3 ^ 2 * 5 * 11
  | .M12 => 2 ^ 6 * 3 ^ 3 * 5 * 11
  | .M22 => 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11
  | .M23 => 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 * 23
  | .M24 => 2 ^ 10 * 3 ^ 3 * 5 * 7 * 11 * 23
  | .J1 => 2 ^ 3 * 3 * 5 * 7 * 11 * 19
  | .J2 => 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7
  | .J3 => 2 ^ 7 * 3 ^ 5 * 5 * 17 * 19
  | .J4 => 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43
  | .HS => 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11
  | .McL => 2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11
  | .He => 2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17
  | .Ru => 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29
  | .Suz => 2 ^ 13 * 3 ^ 7 * 5 ^ 2 * 7 * 11 * 13
  | .ONan => 2 ^ 9 * 3 ^ 4 * 5 * 7 ^ 3 * 11 * 19 * 31
  | .Co1 => 2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 13 * 23
  | .Co2 => 2 ^ 18 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23
  | .Co3 => 2 ^ 10 * 3 ^ 7 * 5 ^ 3 * 7 * 11 * 23
  | .Fi22 => 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13
  | .Fi23 => 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23
  | .Fi24Prime => 2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29
  | .HN => 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19
  | .Ly => 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67
  | .Th => 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31
  | .B => 2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47
  | .M => 0

section Order

theorem card_carrier_eq_d2SporadicOrder (s : TauCeti.SporadicName) (hs : s ≠ .M) :
    Nat.card (NativeSporadic.Carrier s) = d2SporadicOrder s := by
  by_cases hTh : s = .Th
  · subst hTh
    exact CFSG.RankThree.PartOne.CTP.card_Th.trans (by norm_num [d2SporadicOrder])
  · rw [CFSG.EvenSmallLie.Child3.card_carrier s hTh hs]
    cases s <;> first
      | exact absurd rfl hTh
      | exact absurd rfl hs
      | norm_num [CFSG.EvenSmallLie.Child3.sporadicCard, d2SporadicOrder,
          CFSG.Open.monsterBabyOrder]

end Order

section Outer

theorem card_outer_carrier_le_two_of_ne_M (s : TauCeti.SporadicName) (hs : s ≠ .M) :
    Nat.card (Outer (NativeSporadic.Carrier s)) ≤ 2 := by
  cases s
  case M11 => exact CFSG.Sporadic.Schreier.at_m11_schreier.1
  case M12 => exact CFSG.ComponentClassification.M12Cover.card_outer.le
  case M22 => exact CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order.2.1.le
  case M23 => exact CFSG.Sporadic.Schreier.at_m23_schreier.1
  case M24 => exact CFSG.AGLEmbedding.card_outer_M24.le.trans (by norm_num)
  case J1 => exact CFSG.Sporadic.Schreier.at_j1_schreier.1.le.trans (by norm_num)
  case J2 => exact CFSG.Sporadic.Schreier.AT_J2_Schreier.1
  case J3 =>
    exact CFSG.Sporadic.Schreier.outer_card_le_of_equiv
      CFSG.Sporadic.SmallOddCore.j3_outer_card_le CFSG.Sporadic.Schreier.j3PermEquiv
  case J4 => exact CFSG.AGLEmbedding.card_outer_J4.le.trans (by norm_num)
  case HS => exact CFSG.Sporadic.Schreier.HS_outer_card_le_two.1
  case McL => exact CFSG.Sporadic.Schreier.McL_outer_card_le_two.1
  case He => exact CFSG.Sporadic.Schreier.AT_He_Schreier.1
  case Ru =>
    exact CFSG.Sporadic.Schreier.outer_card_le_of_equiv
      (CFSG.Sporadic.RuSchreier.card_outer_ruP.trans_le (by norm_num))
      CFSG.Sporadic.RuSchreier.ruEquivP
  case Suz => exact CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1.le
  case ONan =>
    exact Nat.le_of_dvd two_pos (CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two
      ⟨(MulEquiv.refl _ : NativeSporadic.Carrier .ONan ≃* NativeSporadic.ON)⟩)
  case Co1 => exact CFSG.RankThree.PartOne.SPOR.card_outer_Co1.le.trans (by norm_num)
  case Co2 => exact CFSG.RankThree.PartOne.SPOR.card_outer_Co2.le.trans (by norm_num)
  case Co3 =>
    exact (CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1).le.trans
      (by norm_num)
  case Fi22 => exact CFSG.RankThree.PartOne.card_outer_fi22_carrier.le
  case Fi23 => exact CFSG.Sporadic.FischerOddCore.card_outer_fi23.le.trans (by norm_num)
  case Fi24Prime => exact CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime.le
  case HN => exact CFSG.RankThree.PartOne.SPOR.card_outer_HN.le
  case Ly =>
    exact CFSG.RankThree.PartOne.SPOR.card_outer_Ly.elim (fun h => h.le.trans (by norm_num)) Eq.le
  case Th => exact CFSG.RankThree.PartOne.SPOR.card_outer_Th.le.trans (by norm_num)
  case B => exact CFSG.RankThree.PartOne.SPOR.card_outer_B.le.trans (by norm_num)
  case M => exact absurd rfl hs

end Outer

section Reduction

theorem d2FreeCaseAt_sporadic_of_rows (s : TauCeti.SporadicName) (hs : s ≠ .M) {Pp : ℕ → Prop}
    (hrow : ∀ p, p.Prime → p ≠ 2 → p ^ 2 ∣ d2SporadicOrder s → Pp p →
      ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier s) →
        D2IndexDatumPlus L p) :
    D2FreeCaseAt (.sporadic s) Pp := by
  obtain ⟨f⟩ : Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group) :=
    CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
  refine d2FreeCaseAt_of_datumPlus fun L _ _ ⟨e⟩ p hp hp2 hPp => ?_
  have e' : L ≃* NativeSporadic.Carrier s := e.trans f.symm
  by_cases h : p ^ 2 ∣ d2SporadicOrder s
  · exact hrow p hp hp2 h hPp L ⟨e'⟩
  · refine Or.inl (d2IndexDatum_of_not_sq_dvd hp hp2 ?_ ?_)
    · rw [CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv e']
      exact card_outer_carrier_le_two_of_ne_M s hs
    · rwa [Nat.card_congr e'.toEquiv, card_carrier_eq_d2SporadicOrder s hs]

theorem d2IndexCaseAt_sporadic_of_rows (s : TauCeti.SporadicName) (hs : s ≠ .M) {Pp : ℕ → Prop}
    (hrow : ∀ p, p.Prime → p ≠ 2 → p ^ 2 ∣ d2SporadicOrder s → Pp p →
      ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier s) →
        D2IndexDatumPlus L p) :
    D2IndexCaseAt (.sporadic s) Pp :=
  (d2FreeCaseAt_sporadic_of_rows s hs hrow).indexCaseAt

end Reduction

end CFSG.AGLEmbeddingD2
