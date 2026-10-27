module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerAbstract
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicDFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicEsix
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThreeFamilies
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicTwE6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartOne.AUTSL.OddOutRee
public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
public import CFSG.RankThree.PartOne.MB3.OddOutLinear
public import CFSG.RankThree.PartOne.MB3.OddOutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutOrthogonal
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.OutStructure
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.AGLEmbedding.TwoGenInner (PGoodOut pGoodOut_of_outPNice pGoodOut_of_not_dvd_outer)

section Lie


theorem pGoodOut_three_of_lieModel {K : Type} [Group K] [Finite K]
    (hrk : ∀ A : Subgroup K, CFSG.Open.IsElemAbelian 3 A → Nat.card A ≤ 3)
    {t : StatedLieTag} {n ℓ f : ℕ} (hadm : StatedLieAdmissible t n ℓ f)
    (hmodel : LieModel K t n ℓ f) : PGoodOut 3 K := by
  have nice : OutPNice 3 K → PGoodOut 3 K := pGoodOut_of_outPNice
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hnine : ∀ A : Subgroup K, CFSG.Open.IsElemAbelian 3 A → Nat.card A = 3 ^ 2 → False :=
    fun A hA hc => by
      have := hrk A hA
      rw [hc] at this
      omega
  have hℓ : ℓ.Prime := hadm.1
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    rcases hmodel with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
    · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · by_cases hn : n = 2
        · subst hn
          exact nice (outPNice_PSL_two hp hcl)
        · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hcl
          by_cases hd : 3 ∣ Nat.gcd n (2 ^ f - 1)
          · obtain ⟨A, hA, hc⟩ := exists_nine_of_psl hcl (hd.trans (Nat.gcd_dvd_left _ _))
              (hd.trans (Nat.gcd_dvd_right _ _))
            exact (hnine A hA hc).elim
          · exact nice (outPNice_PSL_ge_three hp hp2 (by omega) hcl hd)
      · by_cases hd : 3 ∣ Nat.gcd n (2 ^ f + 1)
        · obtain ⟨A, hA, hc⟩ := exists_nine_of_psu hcl (hd.trans (Nat.gcd_dvd_left _ _))
            (hd.trans (Nat.gcd_dvd_right _ _))
          exact (hnine A hA hc).elim
        · exact nice (outPNice_PSU hp hcl hd)
      · by_cases hn : n = 2
        · subst hn
          exact nice (outPNice_PSp_two hp hcl)
        · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hcl
          exact nice (outPNice_PSp_ge_three hp (by omega) hcl)
      · obtain ⟨⟨-, -, -, hp2'⟩, -⟩ := id hcl
        exact absurd rfl hp2'
      · obtain ⟨⟨-, -, hn4⟩, -⟩ := id hcl
        by_cases hn : n = 4
        · subst hn
          obtain ⟨A, hA, hc⟩ := exists_nine_of_POmegaPlus_four hcl
          exact (hnine A hA hc).elim
        · exact nice (outPNice_POmegaPlus_ge_five hp hp2 (by omega) hcl)
      · obtain ⟨⟨-, -, hn4⟩, -⟩ := id hcl
        exact nice (outPNice_POmegaMinus hp hp2 hn4 hcl)
    · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact nice (outPNice_G2 hp hch)
      · exact nice (outPNice_F4 hp hch)
      · by_cases h3 : 3 ∣ 2 ^ f - 1
        · obtain ⟨A, hA, hc⟩ := exists_nine_of_E6 hch h3
          exact (hnine A hA hc).elim
        · exact nice (outPNice_E6_three_of_not_dvd hch h3)
      · exact nice (outPNice_E7 hp hch)
      · exact nice (outPNice_E8 hp hch)
      · obtain ⟨A, hA, hc⟩ := exists_nine_of_twistedE6 hch
        exact (hnine A hA hc).elim
      · exact nice (outPNice_trialityD4 hp hch)
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · have h3 : (2 : ℕ) = 3 := hree.1.2.2.2.1
        omega
      · exact nice (outPNice_twistedF4 hp hree)
      · refine pGoodOut_of_not_dvd_outer hp fun hdvd => ?_
        obtain ⟨k, hk⟩ :=
          (Sporadic.Schreier.Tits.AT_Tits_model_Schreier K 2 f hree).1.exists_card_eq
        rw [hk] at hdvd
        have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hdvd)
        omega
    · subst ht
      exact nice (outPNice_Suzuki hp hsz)
  · rcases hmodel with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
    · cases t
      · by_cases hn2 : n = 2
        · subst hn2
          exact nice (outPNice_PSL_two_odd_of_ne_two hp hp2 hℓ2 hcl)
        · have hn3 : 3 ≤ n := by
            have := hcl.1.2.2.1
            omega
          by_cases hd : 3 ∣ Nat.gcd n (ℓ ^ f - 1)
          · obtain ⟨A, hA, hc⟩ := exists_nine_of_psl hcl (hd.trans (Nat.gcd_dvd_left _ _))
              (hd.trans (Nat.gcd_dvd_right _ _))
            exact (hnine A hA hc).elim
          · exact nice (outPNice_PSL_ge_three_odd hp hp2 hn3 hcl hd)
      · by_cases hd : 3 ∣ Nat.gcd n (ℓ ^ f + 1)
        · obtain ⟨A, hA, hc⟩ := exists_nine_of_psu hcl (hd.trans (Nat.gcd_dvd_left _ _))
            (hd.trans (Nat.gcd_dvd_right _ _))
          exact (hnine A hA hc).elim
        · exact nice (outPNice_PSU_odd hp hcl hd)
      · by_cases hn2 : n = 2
        · subst hn2
          exact nice (AUTSL.SpTwo.outPNice_PSp_two_odd hp hp2 hℓ2 hcl)
        · have hn3 : 3 ≤ n := by
            have := hcl.1.2.2.1
            omega
          exact nice (outPNice_PSp_ge_three_odd hp hp2 hn3 hcl)
      · exact nice (outPNice_POmegaOdd_of_ne_two hp hp2 hcl)
      · by_cases hn4 : n = 4
        · subst hn4
          obtain ⟨A, hA, hc⟩ := exists_nine_of_POmegaPlus_four hcl
          exact (hnine A hA hc).elim
        · have hn5 : 5 ≤ n := by
            have := hcl.1.2.2
            omega
          exact nice (outPNice_POmegaPlus_ge_five_of_ne_two hp hp2 hn5 hcl)
      · exact nice (outPNice_POmegaMinus_of_ne_two hp hp2 hcl)
      all_goals exact hcl.2.elim
    · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · by_cases h3 : ℓ = 3
        · subst h3
          exact nice (outPNice_G2_three hp hch)
        · exact nice (outPNice_G2_odd hp hℓ2 h3 hch)
      · exact nice (outPNice_F4_odd hp hℓ2 hch)
      · by_cases h3 : 3 ∣ ℓ ^ f - 1
        · obtain ⟨A, hA, hc⟩ := exists_nine_of_E6 hch h3
          exact (hnine A hA hc).elim
        · exact nice (outPNice_E6_three_of_not_dvd hch h3)
      · exact nice (outPNice_E7_gen hp hp2 hch)
      · exact nice (outPNice_E8_gen hp hch)
      · obtain ⟨A, hA, hc⟩ := exists_nine_of_twistedE6 hch
        exact (hnine A hA hc).elim
      · exact nice (outPNice_trialityD4_odd hp hℓ2 hch)
    · cases t
      case twistedG2 =>
        have h3 : ℓ = 3 := hree.1.2.2.2.1
        subst h3
        exact nice (AUTSL.outPNice_twistedG2 hp hree)
      case twistedF4 => exact absurd hree.1.2.2.2.1 hℓ2
      case Tits => exact absurd hree.1.2.2.2.1 hℓ2
      all_goals
        obtain ⟨-, a, -, hm⟩ := hree
        exact hm.elim
    · exact absurd hsz.1 hℓ2

end Lie

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
