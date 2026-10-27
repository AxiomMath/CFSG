module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutParabolicReduce
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFactParabolic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFactOutDerived
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutSylowLinear
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutSylowUnitary
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutSylowSymplectic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutSylowOrthogonal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutSylowG2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsBase
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.AGLEmbedding


private lemma oddAutSylowFixAt_of_isoLie_G2 {Y : Type} [Group Y] [Finite Y]
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq : q.p = 2)
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) : OddAutSylowFixAt r Y := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
  have hK : 4 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rw [hcard]
    exact CFSG.LocalAnalysis.RankThreeUC.S15.K21dTitsProof.four_le_card_of_p_two hq
      (CFSG.LocalAnalysis.RankThreeUC.S15.K21dTitsProof.card_ne_two_of_valid_G2 hv)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq
    (GaloisField q.p q.exponent) hcard
  exact oddAutSylowFixAt_g2 hK (e.trans b.symm) hr hr5

theorem oddAutSylowFixAt_lieIndex {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hN : ∃ T : Subgroup Y, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ ∧
      ¬ r ∣ Nat.card (Subgroup.normalizer (T : Set Y))) :
    OddAutSylowFixAt r Y := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨T, hT, hN⟩ := hN
  cases d with
  | A n q =>
    change q.p = 2 at hd
    have hC := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hd] at hC
    by_cases hn : n = 1
    · subst hn
      exact oddAutSylowFixAt_psl_two hC hr hr5
    · have hn' : 1 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff (.A n q)).1
        ((TauCeti.LieTypeIndex.valid_iff (.A n q)).1 hv).1).1
      exact oddAutSylowFixAt_psl (by omega) hC hr hr5
        (not_dvd_gcd_of_model_psl hr hr5 hT hN hC)
  | twistedA n q =>
    change q.p = 2 at hd
    have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hv e
    rw [hd] at hC
    exact oddAutSylowFixAt_psu hC hr hr5 (not_dvd_gcd_of_model_psu hr hr5 hT hN hC)
  | B n q =>
    change q.p = 2 at hd
    by_cases hn : n = 2
    · subst hn
      have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at hC
      exact oddAutSylowFixAt_psp hC hr hr5
    · have hn' : 2 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff (.B n q)).1
        ((TauCeti.LieTypeIndex.valid_iff (.B n q)).1 hv).1).1
      have hC := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even n q hv hd
        (by omega) e
      rw [hd] at hC
      exact oddAutSylowFixAt_psp hC hr hr5
  | D n q =>
    change q.p = 2 at hd
    have hC := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even n q hv hd e
    rw [hd] at hC
    exact oddAutSylowFixAt_pomegaPlus hC hr hr5
  | twistedD n q =>
    change q.p = 2 at hd
    have hC := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even
      n q hv hd e
    rw [hd] at hC
    exact oddAutSylowFixAt_pomegaMinus hC hr hr5
  | G2 q =>
    change q.p = 2 at hd
    exact oddAutSylowFixAt_of_isoLie_G2 hv hd e hr hr5
  | C n q => exact hd.elim
  | _ => exact hd.elim


theorem kFactOddAutSylowFix_holds : KFactOddAutSylowFix := by
  intro Y _ _ hsimple hY r hr hr5 hN
  rcases hY with ⟨d, hd, ⟨e⟩⟩ | h2 | h3
  · exact oddAutSylowFixAt_lieIndex d hd e hr hr5 hN
  · exact OddAutSylowFixAt.of_card_outer_le_four hr hr5
      (card_outer_le_four_of_small (Or.inl h2))
  · exact OddAutSylowFixAt.of_card_outer_le_four hr hr5
      (card_outer_le_four_of_small (Or.inr h3))

theorem kFactOddAutParabolicFix_holds : KFactOddAutParabolicFix :=
  kFactOddAutParabolicFix_of_simple
    (kFactOddAutParabolicFixSimple_of_sylowFix kFactLieParabolicClass_holds
      kFactOddAutSylowFix_holds)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
