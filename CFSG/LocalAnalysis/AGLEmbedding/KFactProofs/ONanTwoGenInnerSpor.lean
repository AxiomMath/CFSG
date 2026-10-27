module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerAbstract
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
import CFSG.RankThree.PartOne.SPOR.OuterSimple
import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicBridgeB
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.Sporadic.Schreier.TitsOuterTwo
import CFSG.RankThree.SteinbergCBONOuterPrimes
import CFSG.RankThree.PartOne.KP.Co3Aut
import CFSG.Sporadic.Schreier.PairMcLOut
import CFSG.Sporadic.Schreier.J4SOuter
import CFSG.Sporadic.FischerOddCore.Fi23Aut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadicCases
public import CFSG.Blueprint.Catalog
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.RuDefs

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem pGoodOut_of_alternating {X : Type} [Group X] [Finite X] {m p : ℕ} (hm : 5 ≤ m)
    (hp : p.Prime) (hp5 : 5 ≤ p) (e : X ≃* alternatingGroup (Fin m)) : PGoodOut p X := by
  have hout : Nat.card (Outer X) ≤ 4 :=
    (Nat.card_congr (equivalence e).toEquiv).trans_le
      (CFSG.RankThree.PartOne.card_outer_alternating_le_four hm)
  refine pGoodOut_of_not_dvd_outer hp fun hd => ?_
  have := Nat.le_of_dvd Nat.card_pos hd
  omega

theorem pGoodOut_of_tits
    {X : Type} [Group X] [Finite X] {ℓ f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : ReeTitsModel X .Tits ℓ f) : PGoodOut p X := by
  have hout := (CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound X ℓ f h).2.2.1
  refine pGoodOut_of_not_dvd_outer hp fun hd => ?_
  have := Nat.le_of_dvd Nat.card_pos hd
  omega

theorem outBound_M11 :
    Nat.card (Outer (NativeSporadic.Carrier .M11)) ≤ 4 :=
  (Sporadic.Schreier.at_m11_schreier.1).trans (by norm_num)

theorem outBound_M12 :
    Nat.card (Outer (NativeSporadic.Carrier .M12)) ≤ 4 :=
  Sporadic.Schreier.at_m12_schreier.1

theorem outBound_M22 :
    Nat.card (Outer (NativeSporadic.Carrier .M22)) ≤ 4 :=
  Sporadic.Schreier.at_m22_schreier.1

theorem outBound_M23 :
    Nat.card (Outer (NativeSporadic.Carrier .M23)) ≤ 4 :=
  (Sporadic.Schreier.at_m23_schreier.1).trans (by norm_num)

theorem outBound_M24 :
    Nat.card (Outer (NativeSporadic.Carrier .M24)) ≤ 4 :=
  Sporadic.Schreier.at_m24_schreier.1

theorem outBound_J1 :
    Nat.card (Outer (NativeSporadic.Carrier .J1)) ≤ 4 :=
  (Sporadic.Schreier.at_j1_schreier.1).le.trans (by norm_num)

theorem outBound_J2 :
    Nat.card (Outer (NativeSporadic.Carrier .J2)) ≤ 4 :=
  (Sporadic.Schreier.AT_J2_Schreier.1).trans (by norm_num)

theorem outBound_J3 :
    Nat.card (Outer (NativeSporadic.Carrier .J3)) ≤ 4 :=
  (CFSG.RankThree.PartTwo.Sec4.card_outer_J3).trans (by norm_num)

theorem outBound_HS :
    Nat.card (Outer (NativeSporadic.Carrier .HS)) ≤ 4 :=
  (CFSG.RankThree.PartTwo.Sec4.card_outer_HS).trans (by norm_num)

theorem outBound_McL :
    Nat.card (Outer (NativeSporadic.Carrier .McL)) ≤ 4 :=
  (Sporadic.Schreier.McL_outer_card_le_two.1).trans (by norm_num)

theorem outBound_He :
    Nat.card (Outer (NativeSporadic.Carrier .He)) ≤ 4 :=
  (Sporadic.Schreier.AT_He_Schreier.1).trans (by norm_num)

theorem outBound_Suz :
    Nat.card (Outer (NativeSporadic.Carrier .Suz)) ≤ 4 :=
  (Sporadic.SuzOddCore.outer_carrier_suz.1).le.trans (by norm_num)

theorem outBound_Co3 :
    Nat.card (Outer (NativeSporadic.Carrier .Co3)) ≤ 4 :=
  (CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1).le.trans
    (by norm_num)

theorem outBound_Fi22 :
    Nat.card (Outer (NativeSporadic.Carrier .Fi22)) ≤ 4 :=
  (ComponentClassification.CatalogueOuterTwoPart.card_outer_fi22).le.trans (by norm_num)

theorem outBound_Fi23 :
    Nat.card (Outer (NativeSporadic.Carrier .Fi23)) ≤ 4 :=
  (Sporadic.FischerOddCore.card_outer_fi23).le.trans (by norm_num)

theorem outBound_Fi24Prime :
    Nat.card (Outer (NativeSporadic.Carrier .Fi24Prime)) ≤ 4 :=
  (Sporadic.Schreier.Fi24.card_outer_fi24prime).le.trans (by norm_num)

theorem outBound_Ru :
    Nat.card (Outer (NativeSporadic.Carrier .Ru)) ≤ 4 := by
  rw [show Nat.card (Outer (NativeSporadic.Carrier .Ru)) =
      Nat.card (Outer Sporadic.RuSchreier.ruP) from
    CFSG.RankThree.PartOne.OuterPrimeTwoBridge.card_outer_eq Sporadic.RuSchreier.ruEquivP,
    Sporadic.RuSchreier.card_outer_ruP]
  norm_num

theorem outPrimes_J4
    {T : Type} [Group T]
    (h : Nonempty (T ≃* NativeSporadic.Carrier .J4)) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card (Outer T) → q = 2 ∨ q = 3 :=
  (Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes (T := T) h).1

theorem outPrimes_ONan
    {T : Type} [Group T]
    (h : Nonempty (T ≃* NativeSporadic.Carrier .ONan)) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card (Outer T) → q = 2 ∨ q = 3 := by
  obtain ⟨e⟩ := h
  intro q hq hd
  rw [Nat.card_congr (equivalence e).toEquiv] at hd
  exact Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent q hq hd

theorem sporadic_not_dvd_outer
    {s : TauCeti.SporadicName} {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (hT : Nonempty (T ≃* NativeSporadic.Carrier s)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ Nat.card (Outer T) := by
  obtain ⟨e⟩ := hT
  have hcard : Nat.card (Outer T) = Nat.card (Outer (NativeSporadic.Carrier s)) :=
    Nat.card_congr (equivalence e).toEquiv
  have hpos : 0 < Nat.card (Outer T) := Nat.card_pos
  have keyT : Nat.card (Outer T) ≤ 4 → ¬ p ∣ Nat.card (Outer T) := fun h4 hd => by
    have := Nat.le_of_dvd hpos hd
    omega
  have key : Nat.card (Outer (NativeSporadic.Carrier s)) ≤ 4 → ¬ p ∣ Nat.card (Outer T) :=
    fun h4 => keyT (by rwa [← hcard] at h4)
  have h7 : (s = .Co1 ∨ s = .Co2 ∨ s = .HN ∨ s = .Ly ∨ s = .Th ∨ s = .B ∨ s = .M) →
      ¬ p ∣ Nat.card (Outer T) := fun hs =>
    keyT ((CFSG.RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds s hs T hnab
      ⟨e⟩).trans (by norm_num))
  have hprimes : (∀ q : ℕ, q.Prime → q ∣ Nat.card (Outer T) → q = 2 ∨ q = 3) →
      ¬ p ∣ Nat.card (Outer T) := fun hq hd => by
    rcases hq p hp hd with rfl | rfl <;> omega
  cases s
  · exact key outBound_M11
  · exact key outBound_M12
  · exact key outBound_M22
  · exact key outBound_M23
  · exact key outBound_M24
  · exact key outBound_J1
  · exact key outBound_J2
  · exact key outBound_J3
  · exact hprimes (outPrimes_J4 ⟨e⟩)
  · exact key outBound_HS
  · exact key outBound_McL
  · exact key outBound_He
  · exact key outBound_Ru
  · exact key outBound_Suz
  · exact hprimes (outPrimes_ONan ⟨e⟩)
  · exact h7 (by simp)
  · exact h7 (by simp)
  · exact key outBound_Co3
  · exact key outBound_Fi22
  · exact key outBound_Fi23
  · exact key outBound_Fi24Prime
  · exact h7 (by simp)
  · exact h7 (by simp)
  · exact h7 (by simp)
  · exact h7 (by simp)
  · exact h7 (by simp)

theorem pGoodOut_of_sporadic
    {s : TauCeti.SporadicName} {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (hT : Nonempty (T ≃* NativeSporadic.Carrier s)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : PGoodOut p T :=
  pGoodOut_of_not_dvd_outer hp (sporadic_not_dvd_outer hnab hT hp hp5)

end CFSG.AGLEmbedding.TwoGenInner
