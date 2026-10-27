module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveTransport
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
import CFSG.RankThree.Asc83Table.HS
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall3
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporOrder

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Ru

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

open CFSG.Open CFSG.Blueprint.NativeSporadic Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartTwo.Sec4.RonanK429

theorem false_of_aut_no_e27_model {K S T : Type} [Group K] [Finite K] [Group S] [Finite S]
    [Group T] [IsSimpleGroup T] (hq : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* S)
    (a : K ≃* T) (hout : ¬ 3 ∣ Nat.card (Outer T)) (hno : NoE27 T)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) : False := by
  have : IsSimpleGroup K := a.isSimpleGroup
  have : IsSimpleGroup (K ⧸ center K) := hq.2.1
  have hs : IsSimpleGroup S := e.symm.isSimpleGroup
  have hnab : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hq.2.2
    exact ⟨e x, e y, fun h => hxy (e.injective (by simpa only [map_mul] using h))⟩
  let ψ := (equiv_of_centerQuotient hq e).symm.trans a
  exact autNoE27_of_mulEquiv_of_noE27 ψ hs hnab hout hno E ⟨hE, hc⟩

theorem false_of_hs
    {K S : Type} [Group K] [Finite K] [Group S] [Finite S]
    (hq : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* S) (hK : IsSporadic K .HS)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) : False := by
  obtain ⟨a⟩ := hK
  have : Finite (Carrier .HS) := Finite.of_equiv K a.toEquiv
  have : IsSimpleGroup (Carrier .HS) := CFSG.Sporadic.HS.fam_hs_simplicity.2.2
  have hout : ¬ 3 ∣ Nat.card (Outer (Carrier .HS)) := by
    have h2 : Nat.card (Outer (Carrier .HS)) ≤ 2 :=
      CFSG.RankThree.PartOne.SPOR.card_outer_HS_le_two
    exact fun h => by have := Nat.le_of_dvd (Nat.card_pos : 0 < Nat.card (Outer (Carrier .HS))) h; omega
  exact false_of_aut_no_e27_model hq e a hout
    (noE27_of_not_dvd CFSG.RankThree.Asc83Table.HS.not_dvd_card) hE hc

theorem false_of_he
    {K S : Type} [Group K] [Finite K] [Group S] [Finite S]
    (hq : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* S) (hK : IsSporadic K .He)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) : False := by
  obtain ⟨a⟩ := hK
  have : Finite (Carrier .He) := Finite.of_equiv K a.toEquiv
  have : IsSimpleGroup (Carrier .He) := CFSG.Sporadic.He.isSimpleGroup_He
  have hout : ¬ 3 ∣ Nat.card (Outer (Carrier .He)) := by
    have h2 : Nat.card (Outer (Carrier .He)) ≤ 2 := CFSG.Sporadic.Schreier.AT_He_Schreier.1
    exact fun h => by have := Nat.le_of_dvd (Nat.card_pos : 0 < Nat.card (Outer (Carrier .He))) h; omega
  have hno : NoE27 (Carrier .He) := by
    intro D hD
    have h4 : ¬ 3 ^ 4 ∣ Nat.card (Carrier .He) := by
      change ¬ 3 ^ 4 ∣ Nat.card CFSG.Blueprint.NativeSporadic.He
      rw [CFSG.Sporadic.He.card_He]
      norm_num
    have hr := CFSG.AGLEmbedding.pRank_le_two_of_hasNoncommPair Nat.prime_three h4
      CFSG.AGLEmbedding.hasNoncommPair_three_He
    have h3 := CFSG.SectionRank.le_pRank (p := 3) (k := 3) (by norm_num : 1 < 3) le_top hD.1
      (by simpa using hD.2)
    omega
  exact false_of_aut_no_e27_model hq e a hout hno hE hc

theorem false_of_ru
    {K S : Type} [Group K] [Finite K] [Group S] [Finite S]
    (hq : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* S) (hK : IsSporadic K .Ru)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) : False := by
  obtain ⟨a⟩ := hK
  have : Finite (Carrier .Ru) := Finite.of_equiv K a.toEquiv
  have : IsSimpleGroup (Carrier .Ru) := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have hout : ¬ 3 ∣ Nat.card (Outer (Carrier .Ru)) := by
    exact CFSG.RankThree.PartTwo.Sec4.Item434Spor.not_three_dvd_card_outer_of_le_two
      CFSG.RankThree.PartTwo.Sec4.card_outer_Ru
  have hno : NoE27 (Carrier .Ru) := by
    intro D hD
    have h4 : ¬ 3 ^ 4 ∣ Nat.card (Carrier .Ru) := by
      change ¬ 3 ^ 4 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Ru
      rw [CFSG.Sporadic.Ru.card_Ru]
      norm_num
    have hr := CFSG.AGLEmbedding.pRank_le_two_of_hasNoncommPair Nat.prime_three h4
      CFSG.AGLEmbedding.hasNoncommPair_three_Ru
    have h3 := CFSG.SectionRank.le_pRank (p := 3) (k := 3) (by norm_num : 1 < 3) le_top hD.1
      (by simpa using hD.2)
    omega
  exact false_of_aut_no_e27_model hq e a hout hno hE hc

theorem false_of_j4
    {K S : Type} [Group K] [Finite K] [Group S] [Finite S]
    (hq : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* S) (hK : IsSporadic K .J4)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) : False := by
  obtain ⟨a⟩ := hK
  have : Finite (Carrier .J4) := Finite.of_equiv K a.toEquiv
  have : IsSimpleGroup (Carrier .J4) := CFSG.Sporadic.J4.isSimpleGroup_J4
  have hno : NoE27 (Carrier .J4) := by
    intro D hD
    have h4 : ¬ 3 ^ 4 ∣ Nat.card (Carrier .J4) := by
      change ¬ 3 ^ 4 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J4
      rw [CFSG.Sporadic.J4.card_J4]
      norm_num
    have hr := CFSG.AGLEmbedding.pRank_le_two_of_hasNoncommPair Nat.prime_three h4
      CFSG.AGLEmbedding.hasNoncommPair_three_J4
    have h3 := CFSG.SectionRank.le_pRank (p := 3) (k := 3) (by norm_num : 1 < 3) le_top hD.1
      (by simpa using hD.2)
    omega
  exact false_of_aut_no_e27_model hq e a CFSG.RankThree.PartTwo.Sec4.inputs47Core_outJ4 hno hE hc

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

end
