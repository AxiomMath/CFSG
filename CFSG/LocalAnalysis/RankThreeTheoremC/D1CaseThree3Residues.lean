module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Families
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3SporRank
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3SporSections

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.AGLEmbedding (AltCaseThreeKFacts CatGroup HasKlingenData IsLinTwoIndex
  IsP1ChevTwoIndex IsReeGTwoIndex IsUnitaryIndex KFactKlingenSpFour KFactP1ThreeLie
  KFactUnitaryAutElemRank KFactUnitarySchur KFactUnitarySylowStructure
  ker_conjNormal_eq_centralizer normal_of_forall_isComponentOf_eq
  not_dvd_card_outer_alternatingGroup not_dvd_card_outer_of_quotient)

variable {G : Type} [Group G] [Finite G]

@[expose] def D1CaseThreeJ33 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1ComponentConfig3 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) 3)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
        orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData 3 Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) →
      Subgroup.center K = ⊥ →
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) → False

theorem d1CaseThreeSpor3_of_kFactsE3
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hsec : SporSectionFacts3) (hfacts : SporCaseThreeKFactsRank3E3) (hJ3 : D1CaseThreeJ33 G) :
    D1CaseThreeSpor3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD s ⟨e⟩
  by_cases hs : s ∈ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName)
  · obtain ⟨hsimple, hnonab, -⟩ := hcfg.simple_catalog_center_quotient hK
    exact false_of_mem_sectionExcluded3 hsec hcfg.glob.rank (primeComplementCore (G := H) p)
      hsimple hnonab hs e
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hp : p.Prime := Fact.out
  have : Finite (MulAut K) := MulEquiv.finite_left
  have : Finite (TauCeti.CFSGIndex.sporadic s).Group := Finite.of_equiv _ e.toEquiv
  have : Finite (MulAut (TauCeti.CFSGIndex.sporadic s).Group) := MulEquiv.finite_left
  have hOutQ : ¬ p ∣ Nat.card (Outer (K ⧸ Subgroup.center K)) := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact hOutS s p hp hcfg.red.ne_two
  by_cases hJ : s = .J3 ∧ p = 3 ∧ Subgroup.center K = ⊥
  · obtain ⟨rfl, rfl, hZ⟩ := hJ
    exact hJ3 P M H R Rbar hcfg K hK huniq hnc hcent hKD hZ ⟨e⟩
  · exact false_of_caseThreeKFact3 hcfg hK huniq hnc hcent hKD
      (not_dvd_card_outer_of_quotient hOutQ)
      (hfacts K hK.2.2 s hs ⟨e⟩ p hcfg.red.ne_two (hcfg.isPGroup_center hK)
        (hcfg.isCyclic_center hK huniq) hJ fun T => hcfg.pRank_sylow_le_three T)

@[expose] def D1CaseThreeA3pAt3 (G : Type) [Group G] [Finite G] (S : ℕ → Prop) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    S p → ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      Subgroup.center K = ⊥ →
      Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin (3 * p))) → False

@[expose] def D1CaseThreeA3p3 (G : Type) [Group G] [Finite G] : Prop :=
  D1CaseThreeA3pAt3 G fun _ => True

theorem d1CaseThreeAlt3_of_kFacts (hfacts : AltCaseThreeKFacts) (hres : D1CaseThreeA3p3 G) :
    D1CaseThreeAlt3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD n hn ⟨e⟩
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hp : p.Prime := Fact.out
  have : Finite (MulAut K) := MulEquiv.finite_left
  have hOutQ : ¬ p ∣ Nat.card (Outer (K ⧸ Subgroup.center K)) := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact not_dvd_card_outer_alternatingGroup n hn p hp hcfg.red.ne_two
  by_cases hA : n = 3 * p ∧ Subgroup.center K = ⊥
  · obtain ⟨rfl, hZ⟩ := hA
    exact hres p P M H R Rbar hcfg trivial K hK huniq hnc hcent hKD hZ ⟨e⟩
  · exact false_of_caseThreeKFact3 hcfg hK huniq hnc hcent hKD
      (not_dvd_card_outer_of_quotient hOutQ)
      (hfacts K hK.2.2 n hn ⟨e⟩ p hcfg.red.ne_two (hcfg.isPGroup_center hK)
        (hcfg.isCyclic_center hK huniq) hA)

theorem d1CaseThreeA3p3_of_primes (h3 : D1CaseThreeA3pAt3 G (· = 3))
    (h5 : D1CaseThreeA3pAt3 G (· = 5)) (h7 : D1CaseThreeA3pAt3 G (7 ≤ ·)) :
    D1CaseThreeA3p3 G := by
  intro p _ P M H R Rbar hcfg _ K hK huniq hnc hcent hKD hZ he
  have hp : p.Prime := Fact.out
  have hp2 := hcfg.red.ne_two
  have h4 : p ≠ 4 := fun h => by subst h; norm_num at hp
  have h6 : p ≠ 6 := fun h => by subst h; norm_num at hp
  have := hp.two_le
  by_cases h3' : p = 3
  · exact h3 p P M H R Rbar hcfg h3' K hK huniq hnc hcent hKD hZ he
  by_cases h5' : p = 5
  · exact h5 p P M H R Rbar hcfg h5' K hK huniq hnc hcent hKD hZ he
  exact h7 p P M H R Rbar hcfg (by omega) K hK huniq hnc hcent hKD hZ he

@[expose] def D1CaseThreeLieAt3 (G : Type) [Group G] [Finite G]
    (S : ℕ → TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, S p d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) → False

theorem d1CaseThreeLie3_of_split (hP1 : KFactP1ThreeLie) (hKl : KFactKlingenSpFour)
    (hL2 : D1CaseThreeLieAt3 G fun p d => ∃ n, IsLinTwoIndex p n d)
    (hU : D1CaseThreeLieAt3 G IsUnitaryIndex) (hRee : D1CaseThreeLieAt3 G IsReeGTwoIndex)
    (hC2 : D1CaseThreeLieAt3 G IsP1ChevTwoIndex) : D1CaseThreeLie3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d e
  rcases hP1 p _ Rbar _ hcfg.red hcfg.catalog K hK huniq hnc hcent d e with
    h | h | h | h | h
  · exact hL2 p P M H R Rbar hcfg K hK huniq hnc hcent hKD d h e
  · exact hU p P M H R Rbar hcfg K hK huniq hnc hcent hKD d h e
  · exact hRee p P M H R Rbar hcfg K hK huniq hnc hcent hKD d h e
  · exact hKD (hKl p _ Rbar _ hcfg.red hcfg.catalog K hK huniq hnc hcent d h e)
  · exact hC2 p P M H R Rbar hcfg K hK huniq hnc hcent hKD d h e

theorem d1CaseThreeUnitary3_of_kFacts (hKU1 : KFactUnitarySchur)
    (hKU2 : KFactUnitarySylowStructure) (hKU9 : KFactUnitaryAutElemRank) :
    D1CaseThreeLieAt3 G IsUnitaryIndex := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd ⟨e₁⟩
  have hp : p.Prime := Fact.out
  have : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hZ : Subgroup.center K = ⊥ := hKU1 K p d hd hK.2.2 (hcfg.isPGroup_center hK) ⟨e₁⟩
  have eK : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hL : Nonempty (K ≃* CatGroup d) := ⟨eK.trans e₁⟩
  have hinj : Function.Injective
      (MulAut.conjNormal (H := K) : (H ⧸ primeComplementCore (G := H) p) →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer,
      hcfg.centralizer_eq_bot hK huniq hcent hZ]
  have hle : Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
      2 * d.1.fieldExponent := by
    apply csSup_le'
    rintro k ⟨E, -, hE, hcard⟩
    have h := hKU9 K p d hd hL (E.map MulAut.conjNormal) (elementary_abelian_map p hE _)
    rw [Subgroup.card_map_of_injective hinj, hcard] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  obtain ⟨T₀, hT₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨-, -, -, E, hET, hE, hEcard⟩ := hKU2 K p d hcfg.red.ne_two hd hL T₀
  have hER : E.map K.subtype ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hT₀.le ⟨x, hET hx, rfl⟩).1
  have hge : 2 * d.1.fieldExponent ≤
      Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
    le_csSup (pRank_bddAbove p hp _) ⟨_, hER, elementary_abelian_map p hE _, by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hEcard]⟩
  have h3 := hcfg.pRank_rbar_eq_three
  omega

structure D1CaseThreeKFacts3 : Prop where
  p1Lie : KFactP1ThreeLie
  klingenSpFour : KFactKlingenSpFour
  alt : AltCaseThreeKFacts
  outSpor : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group)
  spor : SporCaseThreeKFactsRank3E3
  sections : SporSectionFacts3
  unitarySchur : KFactUnitarySchur
  unitarySylow : KFactUnitarySylowStructure
  unitaryAutRank : KFactUnitaryAutElemRank

structure D1CaseThreeResidues3 (G : Type) [Group G] [Finite G] : Prop where
  a9 : D1CaseThreeA3pAt3 G (· = 3)
  a15 : D1CaseThreeA3pAt3 G (· = 5)
  a3p : D1CaseThreeA3pAt3 G (7 ≤ ·)
  j3 : D1CaseThreeJ33 G
  linTwo : D1CaseThreeLieAt3 G fun p d => ∃ n, IsLinTwoIndex p n d
  ree : D1CaseThreeLieAt3 G IsReeGTwoIndex
  chevTwo : D1CaseThreeLieAt3 G IsP1ChevTwoIndex

theorem D1CaseThreeResidues3.notKlingen (hk : D1CaseThreeKFacts3) (h : D1CaseThreeResidues3 G) :
    D1CaseThreeNotKlingen3 G :=
  d1CaseThreeNotKlingen3_of_families
    (d1CaseThreeAlt3_of_kFacts hk.alt (d1CaseThreeA3p3_of_primes h.a9 h.a15 h.a3p))
    (d1CaseThreeLie3_of_split hk.p1Lie hk.klingenSpFour h.linTwo
      (d1CaseThreeUnitary3_of_kFacts hk.unitarySchur hk.unitarySylow hk.unitaryAutRank) h.ree
      h.chevTwo)
    (d1CaseThreeSpor3_of_kFactsE3 hk.outSpor hk.sections hk.spor h.j3)

theorem d1CaseThreeResidues3_of_notKlingen (h : D1CaseThreeNotKlingen3 G) :
    D1CaseThreeResidues3 G := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p _ P M H R Rbar hcfg _ K hK huniq hnc hcent hKD _ _
    exact h p P M H R Rbar hcfg K hK huniq hnc hcent hKD
  · intro p _ P M H R Rbar hcfg _ K hK huniq hnc hcent hKD _ _
    exact h p P M H R Rbar hcfg K hK huniq hnc hcent hKD
  · intro p _ P M H R Rbar hcfg _ K hK huniq hnc hcent hKD _ _
    exact h p P M H R Rbar hcfg K hK huniq hnc hcent hKD
  · intro P M H R Rbar hcfg K hK huniq hnc hcent hKD _ _
    exact h 3 P M H R Rbar hcfg K hK huniq hnc hcent hKD
  · intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD _ _ _
    exact h p P M H R Rbar hcfg K hK huniq hnc hcent hKD
  · intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD _ _ _
    exact h p P M H R Rbar hcfg K hK huniq hnc hcent hKD
  · intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD _ _ _
    exact h p P M H R Rbar hcfg K hK huniq hnc hcent hKD

theorem d1CaseThreeResidues3_of_theoremD1 (hD1 : TheoremD1 G) : D1CaseThreeResidues3 G :=
  d1CaseThreeResidues3_of_notKlingen (residues3_of_theoremD1 hD1).2.2.2.2.2

end CFSG.LocalAnalysis.RankThreeTheoremC
