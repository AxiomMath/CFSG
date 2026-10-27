module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcF4Two
public import CFSG.LieType.Chevalley.SimplyLacedSubsystemPerfect
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.Blueprint.Catalog
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LieType.SeitzGeneration.Dispatch
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.CTP.SeitzFineExc
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub Subgroup

variable {τ : Tag} {K : Type} [Field K]

section Certified


theorem subsystemGroup_singleton (i : Fin τ.rank) :
    subsystemGroup τ K {i} = (simpleRootSL2 τ K i).range := by
  rw [range_simpleRootSL2, subsystemGroup]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨j, rfl, c, rfl | rfl⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr ⟨c, rfl⟩
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨i, rfl, c, Or.inl rfl⟩
    · exact ⟨i, rfl, c, Or.inr rfl⟩

theorem exists_sylow_posUnipotent [Finite K] [CharP K 2] :
    ∃ T₀ : Sylow 2 ↥(adjointGroup τ K),
      (T₀ : Subgroup ↥(adjointGroup τ K)) = (posUnipotent τ K).subgroupOf (adjointGroup τ K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (RootWeightDatum.ordinary (K := K) τ).exists_sylow_eq_unipotent 2

theorem leviSubAt_adjointGroup_of_four_le [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {i₀ j₀ : Fin τ.rank} (hij₀ : i₀ ≠ j₀) (hne1 : τ.cartan i₀ j₀ * τ.cartan j₀ i₀ ≠ 1) :
    LeviSubAt ↥(adjointGroup τ K) := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_sylow_posUnipotent (τ := τ) (K := K)
  have hKu : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  obtain ⟨f, hf, hfK⟩ := Nat.exists_prime_and_dvd (show Nat.card Kˣ ≠ 1 by omega)
  have hf2 : f ≠ 2 := fun h => ParSylow.not_two_dvd_card_units K (h ▸ hfK)
  have hf3 : 3 ≤ f := by have := hf.two_le; omega
  have hval : 4 - τ.cartan i₀ j₀ * τ.cartan j₀ i₀ = 4 ∨
      4 - τ.cartan i₀ j₀ * τ.cartan j₀ i₀ = 2 ∨ 4 - τ.cartan i₀ j₀ * τ.cartan j₀ i₀ = 1 := by
    rcases CFSG.LieType.RootSystem.cartan_pair_cases (isFiniteType_cartan τ) hij₀ with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] at hne1 ⊢ <;> omega
  have hdet : ¬ (f : ℤ) ∣ 4 - τ.cartan i₀ j₀ * τ.cartan j₀ i₀ := by
    intro hdvd
    rcases hval with h | h | h <;> rw [h] at hdvd
    · have hf4 : f ∣ 4 := by exact_mod_cast hdvd
      have := Nat.le_of_dvd (by norm_num) hf4
      interval_cases f <;> first | omega | norm_num at hf
    · have := Int.le_of_dvd (by norm_num) hdvd
      omega
    · have := Int.le_of_dvd (by norm_num) hdvd
      omega
  have hfr := EvenTorusRank.two_le_pRank_of_dvd_card_units hf hf2 hfK hij₀ hdet
  have hfSL : f ∣ Nat.card (SL2 K) := by
    rw [show Nat.card (SL2 K) = Nat.card K * (Nat.card K ^ 2 - 1) from
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K]
    have hsq : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
      refine ⟨Nat.card K + 1, ?_⟩
      have h1 : 1 ≤ Nat.card K := by omega
      zify [h1, Nat.one_le_pow 2 (Nat.card K) (by omega)]
      ring
    exact (hfK.trans (hKu ▸ hsq)).trans (dvd_mul_left _ _)
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    haveI := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  refine leviSubAt_of_standard_sylow T₀ fun K₀ p hN => ?_
  rw [hT₀] at hN
  exact leviAt_of_normalizer_le hij₀ hf hf2 hfSL hfr
    (fun C _ hCne hconn _ _ _ _ _ => ConnSubsys.isQuasisimple_subsystemGroup hK4 hCne hconn) hN p

theorem leviSubAt_adjointGroup_two [Finite K] [CharP K 2] (h2 : Nat.card K = 2)
    (hsl : ∀ i j : Fin τ.rank, i ≠ j → τ.cartan i j ≠ 0 →
      τ.cartan i j = -1 ∧ τ.cartan j i = -1)
    {i₀ j₀ : Fin τ.rank} (hij₀ : i₀ ≠ j₀) (h0 : τ.cartan i₀ j₀ = 0) :
    LeviSubAt ↥(adjointGroup τ K) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  obtain ⟨T₀, hT₀⟩ := exists_sylow_posUnipotent (τ := τ) (K := K)
  have hSL : Nat.card (SL2 K) = 6 := by
    rw [show Nat.card (SL2 K) = Nat.card K * (Nat.card K ^ 2 - 1) from
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K, h2]
    norm_num
  have hXcard : ∀ i, Nat.card (subsystemGroup τ K {i}) = 6 := fun i => by
    rw [subsystemGroup_singleton, ← Nat.card_congr
      (MonoidHom.ofInjective (simpleRootSL2_injective_of_charTwo (τ := τ) (K := K) i)).toEquiv,
      hSL]
  have hXG : ∀ i, subsystemGroup τ K {i} ≤ adjointGroup τ K := fun i => by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, -, c, rfl | rfl⟩
    · exact xUnit_mem_adjointGroup j c
    · exact yUnit_mem_adjointGroup j c
  have hcomm : ∀ x ∈ subsystemGroup τ K {i₀}, ∀ y ∈ subsystemGroup τ K {j₀}, Commute x y :=
    SubsysComp.commute_of_cartan_eq_zero (Set.disjoint_singleton.2 hij₀)
      (fun i hi j hj => by rw [hi, hj]; exact h0)
  have hfr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(adjointGroup τ K)) := by
    refine two_le_pRank_of_commuting_subgroups (X₁ := (subsystemGroup τ K {i₀}).subgroupOf _)
      (X₂ := (subsystemGroup τ K {j₀}).subgroupOf _) le_top le_top ?_ ?_ ?_ ?_
    · intro a ha b hb
      exact Subtype.ext (hcomm a ha b hb).eq
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
      have hx₁' : (x : ModGL τ K) ∈ (simpleRootSL2 τ K i₀).range := by
        rw [← subsystemGroup_singleton]; exact hx₁
      obtain ⟨A, hA⟩ := hx₁'
      have hAc : A ∈ Subgroup.center (SL2 K) := by
        rw [Subgroup.mem_center_iff]
        intro B
        apply simpleRootSL2_injective_of_charTwo i₀
        rw [map_mul, map_mul, hA]
        have hB : simpleRootSL2 τ K i₀ B ∈ subsystemGroup τ K {i₀} := by
          rw [subsystemGroup_singleton]; exact ⟨B, rfl⟩
        exact (hcomm _ hB _ hx₂).eq
      obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hAc
      rw [Fintype.card_fin, pow_two] at hr
      rw [eq_one_of_mul_self_eq_one_of_charTwo hr, map_one] at hrA
      have hA1 : A = 1 := Subtype.ext hrA.symm
      rw [Subgroup.mem_bot]
      exact Subtype.ext (by rw [← hA, hA1, map_one]; rfl)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hXG i₀)).toEquiv, hXcard]
      norm_num
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hXG j₀)).toEquiv, hXcard]
      norm_num
  refine leviSubAt_of_standard_sylow T₀ fun K₀ p hN => ?_
  rw [hT₀] at hN
  refine leviAt_of_normalizer_le hij₀ Nat.prime_three (by norm_num) (by rw [hSL]; norm_num) hfr
    ?_ hN p
  intro C _ hCne hconn q hq h5 hqC _
  by_cases hsing : ∃ i, C = {i}
  · exfalso
    obtain ⟨i, rfl⟩ := hsing
    rw [hXcard] at hqC
    have := Nat.le_of_dvd (by norm_num) hqC
    interval_cases q <;> first | omega | norm_num at hq
  · refine ConnSubsys.isQuasisimple_subsystemGroup_of_isPerfect
      (SLPerfect.isPerfect_subsystemGroup_of_simplyLaced fun i hi => ?_) hCne hconn
    by_contra hno
    push Not at hno
    apply hsing
    refine ⟨i, Set.Subset.antisymm ?_ (Set.singleton_subset_iff.2 hi)⟩
    refine hconn {i} ⟨i, hi, rfl⟩ fun a ha b hb haS hab hc => ?_
    rw [Set.mem_singleton_iff] at haS
    subst haS
    exact absurd (hsl a b hab hc).2 (hno b hb (hsl a b hab hc).1)

end Certified

section Fields


theorem leviSubAt_of_untwistedChevalleyModel {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : UntwistedChevalleyModel S τ (2 ^ f))
    (h : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
      LeviSubAt ↥(adjointGroup τ K)) :
    LeviSubAt S := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
  haveI : CharP K 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  exact LeviSubAt.of_mulEquiv
    (e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)) (h K hK)

theorem four_le_two_pow_of_ne {f : ℕ} (h : 2 ^ f ≠ 2) (h1 : 2 ^ f ≠ 1) : 4 ≤ 2 ^ f := by
  rcases f with _ | _ | f
  · simp at h1
  · simp at h
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem leviSubAt_g2 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : ChevalleyExceptionalModel S .G2 2 f) : LeviSubAt S := by
  obtain ⟨⟨-, hq⟩, hu⟩ := hm
  refine leviSubAt_of_untwistedChevalleyModel hu fun K _ _ _ hK => ?_
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    refine four_le_two_pow_of_ne (fun h => ?_) (fun h => ?_) <;> omega
  exact leviSubAt_adjointGroup_of_four_le h4 (i₀ := ⟨0, by decide⟩) (j₀ := ⟨1, by decide⟩)
    (by decide) (by decide)

theorem leviSubAt_f4 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : ChevalleyExceptionalModel S .F4 2 f) : LeviSubAt S := by
  obtain ⟨-, hu⟩ := hm
  refine leviSubAt_of_untwistedChevalleyModel hu fun K _ _ _ hK => ?_
  by_cases h2 : Nat.card K = 2
  · exact leviSubAt_adjointGroup_F4_two h2
  · have h1 : Nat.card K ≠ 1 := Finite.one_lt_card.ne'
    have h4 : 4 ≤ Nat.card K := hK ▸ four_le_two_pow_of_ne (hK ▸ h2) (hK ▸ h1)
    exact leviSubAt_adjointGroup_of_four_le h4 (i₀ := ⟨0, by decide⟩) (j₀ := ⟨2, by decide⟩)
      (by decide) (by decide)

theorem leviSubAt_of_simplyLaced {S : Type} [Group S] [Finite S] {f : ℕ}
    (hu : UntwistedChevalleyModel S τ (2 ^ f))
    (hsl : ∀ i j : Fin τ.rank, i ≠ j → τ.cartan i j ≠ 0 →
      τ.cartan i j = -1 ∧ τ.cartan j i = -1)
    {i₀ j₀ : Fin τ.rank} (hij₀ : i₀ ≠ j₀) (h0 : τ.cartan i₀ j₀ = 0) : LeviSubAt S := by
  refine leviSubAt_of_untwistedChevalleyModel hu fun K _ _ _ hK => ?_
  by_cases h2 : Nat.card K = 2
  · exact leviSubAt_adjointGroup_two h2 hsl hij₀ h0
  · have h1 : Nat.card K ≠ 1 := Finite.one_lt_card.ne'
    have h4 : 4 ≤ Nat.card K := hK ▸ four_le_two_pow_of_ne (hK ▸ h2) (hK ▸ h1)
    exact leviSubAt_adjointGroup_of_four_le h4 hij₀ (by rw [h0]; norm_num)

theorem leviSubAt_e6 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : ChevalleyExceptionalModel S .E6 2 f) : LeviSubAt S := by
  obtain ⟨-, hu⟩ := hm
  refine leviSubAt_of_simplyLaced hu ?_ (i₀ := ⟨0, by decide⟩) (j₀ := ⟨1, by decide⟩)
    (by decide) (by decide)
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem leviSubAt_e7 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : ChevalleyExceptionalModel S .E7 2 f) : LeviSubAt S := by
  obtain ⟨-, hu⟩ := hm
  refine leviSubAt_of_simplyLaced hu ?_ (i₀ := ⟨0, by decide⟩) (j₀ := ⟨1, by decide⟩)
    (by decide) (by decide)
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem leviSubAt_e8 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : ChevalleyExceptionalModel S .E8 2 f) : LeviSubAt S := by
  obtain ⟨-, hu⟩ := hm
  refine leviSubAt_of_simplyLaced hu ?_ (i₀ := ⟨0, by decide⟩) (j₀ := ⟨1, by decide⟩)
    (by decide) (by decide)
  intro i j
  fin_cases i <;> fin_cases j <;> decide

end Fields

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc
