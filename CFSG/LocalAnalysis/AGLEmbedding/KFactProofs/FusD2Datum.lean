module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.FusionCase
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2M22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2M23
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2HS
public import CFSG.RankThree.PartOne.CTP.SporadicFusion
public import CFSG.RankThree.PartOne.CTP.SporadicFusionSuz
public import CFSG.RankThree.PartOne.CTP.SporadicFusionTh
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
public import CFSG.RankThree.PartTwo.Sec4.Item47Native
public import CFSG.Sporadic.SuzOddCore.Outer

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.CTP.Fus
  CFSG.Blueprint CFSG.AGLEmbedding

theorem d2IndexDatum_of_fusion {K L : Type} [Group K] [Group L] [Finite L] (e : L ≃* K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hOut : Nat.card (Outer K) ≤ 2)
    (h3 : ¬ p ^ 3 ∣ Nat.card K) (hfus : FusionGenerationOf K p) : D2IndexDatum L p := by
  have hK : Finite K := Finite.of_equiv L e.toEquiv
  refine ⟨?_, Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))⟩
  · rw [CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv e]
    intro hdvd
    have : Finite (MulAut K) := MulEquiv.finite_left
    have h1 := Nat.le_of_dvd Nat.card_pos hdvd
    have h2 := hp.two_le
    omega
  · rwa [Nat.card_congr e.toEquiv]
  · exact CFSG.AGLEmbedding.fusionGenerationOf_of_mulEquiv e.symm hfus

theorem d2IndexDatum_M22_three
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .M22) :
    D2IndexDatum L 3 :=
  d2IndexDatum_of_fusion e Nat.prime_three (by norm_num)
    (by
      have : Finite (NativeSporadic.Carrier .M22) := inferInstanceAs (Finite NativeSporadic.M22)
      exact CFSG.RankThree.PartTwo.Sec4.card_outer_le_two_of_card_mulAut_le
        CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card)
    (by
      rw [show Nat.card (NativeSporadic.Carrier .M22) = 443520 from
        CFSG.Sporadic.Mathieu.card_M22]
      norm_num)
    (fusionGenerationOf_M22_three)

theorem d2IndexDatum_M23_three
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .M23) :
    D2IndexDatum L 3 :=
  d2IndexDatum_of_fusion e Nat.prime_three (by norm_num)
    ((CFSG.Sporadic.Schreier.at_m23_schreier).1)
    (by
      rw [show Nat.card (NativeSporadic.Carrier .M23) = 10200960 from
        CFSG.RankThree.PartOne.CTP.card_M23]
      norm_num)
    (fusionGenerationOf_M23_three)

theorem d2IndexDatum_J2_five
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .J2) :
    D2IndexDatum L 5 :=
  d2IndexDatum_of_fusion e Nat.prime_five (by norm_num)
    (CFSG.RankThree.PartTwo.Sec4.card_outer_J2)
    (by
      rw [show Nat.card (NativeSporadic.Carrier .J2) = 604800 from
        CFSG.Sporadic.J2.card_J2]
      norm_num)
    (CFSG.RankThree.PartOne.CTP.fusionGenerationOf_J2)

theorem d2IndexDatum_He_five
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .He) :
    D2IndexDatum L 5 :=
  d2IndexDatum_of_fusion e Nat.prime_five (by norm_num)
    ((CFSG.Sporadic.Schreier.AT_He_Schreier).1)
    (by
      rw [show Nat.card (NativeSporadic.Carrier .He) = 4030387200 from
        CFSG.Sporadic.He.card_He]
      norm_num)
    (CFSG.RankThree.PartOne.CTP.fusionGenerationOf_He)

theorem d2IndexDatum_Suz_five
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .Suz) :
    D2IndexDatum L 5 :=
  d2IndexDatum_of_fusion e Nat.prime_five (by norm_num)
    ((CFSG.Sporadic.SuzOddCore.outer_carrier_suz).1.le)
    (by
      rw [show Nat.card (NativeSporadic.Carrier .Suz) = 448345497600 from
        CFSG.Sporadic.Suz.card_Suz]
      norm_num)
    (CFSG.RankThree.PartOne.CTP.fusionGenerationOf_Suz)

theorem d2IndexDatum_Th_seven
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .Th) :
    D2IndexDatum L 7 :=
  d2IndexDatum_of_fusion e (by norm_num) (by norm_num)
    ((CFSG.RankThree.PartOne.SPOR.card_outer_Th).le.trans (by norm_num))
    (by
      rw [show Nat.card (NativeSporadic.Carrier .Th) = 90745943887872000 from
        CFSG.RankThree.PartOne.CTP.card_Th]
      norm_num)
    (CFSG.RankThree.PartOne.CTP.fusionGenerationOf_Th)

theorem d2IndexDatum_HS_three
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .HS) :
    D2IndexDatum L 3 :=
  d2IndexDatum_of_fusion e Nat.prime_three (by norm_num)
    (CFSG.RankThree.PartTwo.Sec4.card_outer_HS)
    (by
      rw [show Nat.card (NativeSporadic.Carrier .HS) = 44352000 from
        CFSG.Sporadic.HS.card_HS]
      norm_num)
    (fusionGenerationOf_HS_three)

end CFSG.AGLEmbeddingD2
