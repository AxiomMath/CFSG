module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthD4GraphReduce
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthD4GraphHH
public import Certificates.Certificate43
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate3951
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthD4GraphField
import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Glue
import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Shintani
import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.ThreeD4
import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.G2Class
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.ClassOne
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.Chevalley.SteinbergBID4TrialityDescent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three
open CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

theorem s2019OrthD4GraphType_holds :
    S2019OrthD4GraphType := by
  intro K _ _ q f hq hq2 hq3 hcard α hα3 g a ε hε3 hε0 hα
  have hchar : ringChar K = q := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hpr, hn⟩ := FiniteField.card K (ringChar K)
    have hf : f ≠ 0 := by
      rintro rfl
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hcard, pow_zero] at h1
      exact lt_irrefl 1 h1
    have hdvd : q ∣ ringChar K ^ (n : ℕ) := by
      rw [← hn, ← Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self q hf
    exact ((Nat.prime_dvd_prime_iff_eq hq hpr).1 (hq.dvd_of_dvd_pow hdvd)).symm
  have hK2 : ringChar K ≠ 2 := by rw [hchar]; exact hq2
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; exact hq3
  have h5 : 5 ≤ ringChar K := by
    rw [hchar]
    exact hq.five_le_of_ne_two_of_ne_three hq2 hq3
  have hT : CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType α
      fun ε σ => ε ≠ 0 ∧ σ = 1 :=
    ⟨g, a, 1, ε, hε3, one_pow 3, ⟨hε0, rfl⟩, hα⟩
  rcases ClassOdd.d4GraphClassOdd_of (ClassOdd.graphShintaniNF_of ClassOdd.threeD4FixedNF_holds)
      ClassOdd.g2ThreeClass_holds K h5 α hα3 hT with ⟨ψ, hψ⟩ | ⟨ψ, B, hB3, hB1, hψ⟩
  · refine s2019FixCentralizes_of_conj Nat.prime_three ψ α ?_
    rcases hψ with h | h
    · rw [h]
      exact s2019FixCentralizes_d4Graph_one hK2 hK3
    · rw [h]
      intro L hL
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_d4Graph_two] at hL
      exact s2019FixCentralizes_d4Graph_one hK2 hK3 L hL
  · refine s2019FixCentralizes_of_conj Nat.prime_three ψ α ?_
    rcases hψ with h | h
    · rw [h]
      exact s2019FixCentralizes_gammaP hK2 hK3 hB3 hB1
    · rw [h]
      apply s2019FixCentralizes_of_inv
      rw [inv_inv]
      exact s2019FixCentralizes_gammaP hK2 hK3 hB3 hB1

end CFSG.LocalAnalysis.GLTheoremA.S2019
