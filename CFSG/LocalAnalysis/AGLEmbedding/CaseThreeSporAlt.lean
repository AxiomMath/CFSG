module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKill
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def D1CaseThreeJ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 3)] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1ComponentConfig 3 P M H R Rbar →
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

@[expose] def SporCaseThreeKFacts : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → ∀ s : TauCeti.SporadicName,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → IsPGroup p (Subgroup.center K) →
      IsCyclic (Subgroup.center K) → ¬ (s = .J3 ∧ p = 3 ∧ Subgroup.center K = ⊥) →
      CaseThreeKFact p K

theorem d1CaseThreeSpor_of_kFacts (hS2 : S2Lemma) (hKl : KlingenTransport)
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hfacts : SporCaseThreeKFacts) (hJ3 : D1CaseThreeJ3) : D1CaseThreeSpor := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD s ⟨e⟩
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
    exact hJ3 G P M H R Rbar hcfg K hK huniq hnc hcent hKD hZ ⟨e⟩
  · exact false_of_caseThreeKFact hcfg hK huniq hnc hcent hKD
      (not_dvd_card_outer_of_quotient hOutQ) hS2 hKl
      (hfacts K hK.2.2 s ⟨e⟩ p hcfg.red.ne_two (hcfg.isPGroup_center hK)
        (isCyclic_center_of_config hcfg hK huniq) hJ)

theorem d1CaseThreeSpor_of_kFacts' (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime →
      p ≠ 2 → ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hfacts : SporCaseThreeKFacts) (hJ3 : D1CaseThreeJ3) : D1CaseThreeSpor :=
  d1CaseThreeSpor_of_kFacts s2Lemma klingenTransport hOutS hfacts hJ3

@[expose] def D1CaseThreeA3p : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
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

@[expose] def AltCaseThreeKFacts : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → ∀ n : ℕ, 5 ≤ n →
    Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) →
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → IsPGroup p (Subgroup.center K) →
      IsCyclic (Subgroup.center K) → ¬ (n = 3 * p ∧ Subgroup.center K = ⊥) →
      CaseThreeKFact p K

theorem d1CaseThreeAlt_of_kFacts (hS2 : S2Lemma) (hKl : KlingenTransport)
    (hOutA : ∀ n : ℕ, 5 ≤ n → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (alternatingGroup (Fin n))))
    (hfacts : AltCaseThreeKFacts) (hres : D1CaseThreeA3p) : D1CaseThreeAlt := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD n hn ⟨e⟩
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hp : p.Prime := Fact.out
  have : Finite (MulAut K) := MulEquiv.finite_left
  have hOutQ : ¬ p ∣ Nat.card (Outer (K ⧸ Subgroup.center K)) := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact hOutA n hn p hp hcfg.red.ne_two
  by_cases hA : n = 3 * p ∧ Subgroup.center K = ⊥
  · obtain ⟨rfl, hZ⟩ := hA
    exact hres G p P M H R Rbar hcfg K hK huniq hnc hcent hKD hZ ⟨e⟩
  · exact false_of_caseThreeKFact hcfg hK huniq hnc hcent hKD
      (not_dvd_card_outer_of_quotient hOutQ) hS2 hKl
      (hfacts K hK.2.2 n hn ⟨e⟩ p hcfg.red.ne_two (hcfg.isPGroup_center hK)
        (isCyclic_center_of_config hcfg hK huniq) hA)

theorem d1CaseThreeAlt_of_kFacts' (hOutA : ∀ n : ℕ, 5 ≤ n → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (alternatingGroup (Fin n))))
    (hfacts : AltCaseThreeKFacts) (hres : D1CaseThreeA3p) : D1CaseThreeAlt :=
  d1CaseThreeAlt_of_kFacts s2Lemma klingenTransport hOutA hfacts hres

@[expose] def A3pGuestLift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      Subgroup.center K = ⊥ →
      Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin (3 * p))) →
      7 ≤ p → 3 ∈ GLBBetaFour G ∧ 3 ≤ Open.pRank 3 (H ⊓ M)

theorem d1CaseThreeA3p_of_guest (hlift : A3pGuestLift)
    (h15 : ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 5)] (P : Sylow 5 G)
      (M H R : Subgroup G) (Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5)),
      D1ComponentConfig 5 P M H R Rbar →
      ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 5), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 5), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) 5)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 5)),
        orderOf c = 5 → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData 5 Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5))) →
      Subgroup.center K = ⊥ → Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 15)) →
      False)
    (h9 : ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 3)] (P : Sylow 3 G)
      (M H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)),
      D1ComponentConfig 3 P M H R Rbar →
      ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) 3)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
        orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData 3 Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) →
      Subgroup.center K = ⊥ → Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 9)) →
      False) : D1CaseThreeA3p := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD hZ he
  have hp : p.Prime := Fact.out
  have hp2 := hcfg.red.ne_two
  by_cases h3 : p = 3
  · subst h3
    exact h9 G P M H R Rbar hcfg K hK huniq hnc hcent hKD hZ he
  by_cases h5 : p = 5
  · subst h5
    exact h15 G P M H R Rbar hcfg K hK huniq hnc hcent hKD hZ he
  have h7 : 7 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h => by subst h; norm_num at hp
    have h6 : p ≠ 6 := fun h => by subst h; norm_num at hp
    omega
  obtain ⟨hq, hrank⟩ := hlift G p P M H R Rbar hcfg K hK huniq hZ he h7
  exact false_of_guestPrime hcfg.glob.pre hq (hcfg.ind 3 hq (by omega)) hcfg.loc.maxLocal
    hcfg.ext.maxTwoLocal_H hcfg.ext.not_le hrank

section Data

open CFSG.RankThree.PartOne.StrongP

@[expose] def KernelTrivialAt (X : Type) [Group X] (p : ℕ) : Prop :=
  ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* X), Function.Surjective π →
    π.ker ≤ Subgroup.center E → IsPGroup p π.ker → π.ker = ⊥

@[expose] def CoverWeakGen (X : Type) [Group X] (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (π : K →* X), Function.Surjective π →
    π.ker = Subgroup.center K → Group.IsPerfect K → Subgroup.center K ≠ ⊥ →
    IsPGroup p (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    ∀ T : Sylow p K, GLBWeakCore p (T : Subgroup K) = ⊤

@[expose] def SporCaseThreePrimeData (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime] :
    Prop :=
  ¬ p ^ 3 ∣ Nat.card X ∨
    (¬ p ^ 4 ∣ Nat.card X ∧ HasNoncommPair p X ∧ KernelTrivialAt X p) ∨
    ((∀ T : Sylow p X, GLBWeakCore p (T : Subgroup X) = ⊤ ∨ KlingenAlt p X T) ∧
      (KernelTrivialAt X p ∨ CoverWeakGen X p))

@[expose] def SporadicCaseThreeData (X : Type) [Group X] : Prop :=
  Nat.card X ≠ 0 ∧ ∀ [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 → SporCaseThreePrimeData X p

@[expose] def SporadicCaseThreeDataJ3 (X : Type) [Group X] : Prop :=
  Nat.card X ≠ 0 ∧ ∀ [Finite X],
    (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ 3 → SporCaseThreePrimeData X p) ∧
    @CoverWeakGen X _ 3 ⟨Nat.prime_three⟩

@[expose] def MonsterCaseThreeData : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .M) → SporadicCaseThreeData T

@[expose] def KFactsFromData : Prop :=
  (∀ s : TauCeti.SporadicName,
      Nonempty (Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group)) →
    (∀ s : TauCeti.SporadicName, s ≠ .J3 → s ≠ .M →
      SporadicCaseThreeData (Blueprint.NativeSporadic.Carrier s)) →
    SporadicCaseThreeDataJ3 (Blueprint.NativeSporadic.Carrier .J3) →
    MonsterCaseThreeData → SporCaseThreeKFacts

@[expose] def TCGenDatum (X : Type) [Group X] [Finite X] (p : ℕ) : Prop :=
  ∃ (r : ℕ) (U : Fin r → Subgroup X) (P : Subgroup X) (S : Set X), IsPGroup p P ∧
    (∀ i, U i ≤ P) ∧ (∀ i, 2 ≤ Open.pRank p (U i) ∧
      3 ≤ Open.pRank p (U i ⊔ (P ⊓ Subgroup.centralizer (U i : Set X)))) ∧
    Subgroup.closure S = ⊤ ∧
    ∀ g ∈ S, ∃ i, g ∈ Subgroup.normalizer (U i : Set X)

@[expose] def RankThreeDatum (X : Type) [Group X] (p : ℕ) : Prop :=
  ∃ (r : ℕ) (D : Fin r → ModuleSpec X p) (P : Subgroup X), IsPGroup p P ∧
    (∀ i, (D i).span ≤ P) ∧ (∀ i, 3 ≤ (D i).n ∧ (D i).NoAlt) ∧
    Subgroup.closure (⋃ i, Set.range (D i).g) = ⊤

@[expose] def CoverPointDatum (X : Type) [Group X] (p : ℕ) : Prop :=
  ∃ (D : ModuleSpec X p) (k : ℕ) (b : Fin k → X) (l : Fin k → ℕ)
    (h : (j : Fin k) → Fin (l j) → X) (e : (j : Fin k) → Fin (l j) → ℕ),
    (3 ≤ D.n ∨ (2 ≤ D.n ∧ D.NoAlt)) ∧ D.NoFun ∧ (∀ j, b j ∈ D.span ∧ b j ≠ 1) ∧
    (∀ j i, h j i * b j * (h j i)⁻¹ = b j ^ e j i) ∧
    Subgroup.closure (Set.range D.g ∪ ⋃ j, Set.range (h j)) = ⊤

theorem weakCoreOfTC :
    ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], TCGenDatum X p →
      ∀ T : Sylow p X, GLBWeakCore p (T : Subgroup X) = ⊤ := by
  intro X _ _ p _ hdat T
  obtain ⟨r, U, P, S, hP, hUP, hU, hS, hSU⟩ := hdat
  have hp : p.Prime := Fact.out
  obtain ⟨T', hT'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X T' T
  let c := (MulAut.conj g).toMonoidHom
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hT : (T : Subgroup X) = (T' : Subgroup X).map c := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hcC : ∀ (V : Subgroup X), (Subgroup.centralizer (V : Set X)).map c ≤
      Subgroup.centralizer ((V.map c : Subgroup X) : Set X) := by
    intro V
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp hy v hv
    simp only [c, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * v * g⁻¹ * (g * y * g⁻¹) = g * (v * y) * g⁻¹ := by group
      _ = g * (y * v) * g⁻¹ := by rw [h]
      _ = g * y * g⁻¹ * (g * v * g⁻¹) := by group
  have hN : ∀ i, (Subgroup.normalizer (U i : Set X)).map c ≤
      GLBWeakCore p (T : Subgroup X) := by
    intro i
    have hQT : (U i).map c ≤ (T : Subgroup X) := hT ▸ Subgroup.map_mono ((hUP i).trans hT')
    have h2 : 2 ≤ Open.pRank p ((U i).map c) :=
      (hU i).1.trans (SectionRank.pRank_le_map hp.one_lt c hcinj _)
    have hmap : (U i ⊔ (P ⊓ Subgroup.centralizer (U i : Set X))).map c ≤ (U i).map c ⊔
        ((T : Subgroup X) ⊓ Subgroup.centralizer (((U i).map c : Subgroup X) : Set X)) := by
      rw [Subgroup.map_sup]
      refine sup_le_sup_left ?_ _
      refine (Subgroup.map_inf_le _ _ _).trans (inf_le_inf ?_ (hcC _))
      exact hT ▸ Subgroup.map_mono hT'
    have h3 : 3 ≤ Open.pRank p ((U i).map c ⊔
        ((T : Subgroup X) ⊓ Subgroup.centralizer (((U i).map c : Subgroup X) : Set X))) :=
      ((hU i).2.trans (SectionRank.pRank_le_map hp.one_lt c hcinj _)).trans
        (PreuniquenessRankFour.Helpers.pRank_mono p hp hmap)
    exact (Subgroup.le_normalizer_map c).trans
      (PreuniquenessRankFour.Helpers.normalizer_le_weakCore p hQT h2 h3)
  have hle : (Subgroup.closure S).map c ≤ GLBWeakCore p (T : Subgroup X) := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨i, hi⟩ := hSU s hs
    exact hN i (Subgroup.mem_map_of_mem c hi)
  rw [hS, Subgroup.map_top_of_surjective c (MulAut.conj g).surjective] at hle
  exact eq_top_iff.mpr hle

end Data

theorem d1CaseThreeSpor_of_data (hKF : KFactsFromData)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hdata : ∀ s : TauCeti.SporadicName, s ≠ .J3 → s ≠ .M →
      SporadicCaseThreeData (Blueprint.NativeSporadic.Carrier s))
    (hJ3data : SporadicCaseThreeDataJ3 (Blueprint.NativeSporadic.Carrier .J3))
    (hM : MonsterCaseThreeData)
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hJ3 : D1CaseThreeJ3) : D1CaseThreeSpor :=
  d1CaseThreeSpor_of_kFacts' hOutS (hKF hbr hdata hJ3data hM) hJ3

end CFSG.AGLEmbedding
