module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.Sporadic.ONOddCore.Block
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import Certificates.Certificate9475

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem on_beta_fus3_check :
    fusCheck (ops3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2
      betaONP3N betaONP3Prog betaONP3 = true :=
  Certificates.certificate9475

theorem fusionGenerationOf_ON_three :
    FusionGenerationOf NativeSporadic.ON 3 :=
  fusionGenerationOf_of_check (spec3 154) (D := betaONP3) Nat.prime_three on_beta_fus3_check

theorem sporadicBetaData_ONan :
    SporadicBetaData (NativeSporadic.Carrier .ONan) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .ONan)) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two
    ⟨MulEquiv.refl _⟩)
  refine sporadicBetaData_of_card
    CFSG.Sporadic.ONOddCore.card_native_ON (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 460815505920 = {2, 3, 5, 7, 11, 19, 31} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_ON_three),
    fun _ => Or.inl (by norm_num), fun _ => Or.inr (Or.inl ⟨by norm_num, hasNoncommPair_ON⟩),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
