module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGPara
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGStrong

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

@[expose] def KGSteps56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → ∀ H S : Subgroup G, Optimal p M x z H S →
      GLBPrimeCore p H ≤ M →
      (∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
        ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) →
      ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G)) →
      IsPGroup 2 (GLBPrimeCore p H) → ∀ L : Subgroup G,
        ∀ [((GLBPrimeCore p H).subgroupOf H).Normal],
          KGC.KGData3 p H (GLBPrimeCore p H) S (zpowers x ⊔ zpowers z) L M z →
          KGC.KGStrongEmb p M z →
          KGStep4Concl (KGC.QA H (GLBPrimeCore p H)) (KGC.img H (GLBPrimeCore p H) L)
            (KGC.img H (GLBPrimeCore p H) S) → False

@[expose] def KGLocal
    (Case : ∀ (A : Type) [Group A] [Finite A], Subgroup A → Subgroup A → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → ∀ H S : Subgroup G, Optimal p M x z H S →
      GLBPrimeCore p H ≤ M →
      (∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
        ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) →
      ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G)) →
      IsPGroup 2 (GLBPrimeCore p H) → ∀ L : Subgroup G,
        ∀ [((GLBPrimeCore p H).subgroupOf H).Normal],
          KGC.KGData3 p H (GLBPrimeCore p H) S (zpowers x ⊔ zpowers z) L M z →
          KGC.KGStrongEmb p M z →
          KGStep4Concl (KGC.QA H (GLBPrimeCore p H)) (KGC.img H (GLBPrimeCore p H) L)
            (KGC.img H (GLBPrimeCore p H) S) →
          Case (KGC.QA H (GLBPrimeCore p H)) (KGC.img H (GLBPrimeCore p H) L)
            (KGC.img H (GLBPrimeCore p H) S) → False

@[expose] def KGStep5Sylow : Prop :=
  KGLocal fun A _ _ Kb Sb => Sb ⊓ Kb ≠ ⊥ ∧ CFSG.ABGLocalTools.IsSylowOf 2 (Sb ⊓ Kb) Kb ∧
    ¬ fusionIsBenderGroup ↥Kb

@[expose] def KGStep5Para : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (Kb Sb Bb Mb : Subgroup A) (z : A),
    KQCfg A p Kb Sb Bb Mb z → KQStrongEmb A p Mb z → KGStep4Concl A Kb Sb → Sb ⊓ Kb ≠ ⊥ →
      ¬ CFSG.ABGLocalTools.IsSylowOf 2 (Sb ⊓ Kb) Kb → False

@[expose] def KGStep6 : Prop :=
  KGLocal fun A _ _ Kb Sb => Sb ⊓ Kb = ⊥

@[expose] def KGStep6Noncyc : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (Kb Sb Bb Mb : Subgroup A) (z : A),
    KQCfg A p Kb Sb Bb Mb z → KGStep4Concl A Kb Sb → Sb ⊓ Kb = ⊥ → ¬ IsCyclic ↥Sb → False

@[expose] def KGStep6Cyc : Prop :=
  KGLocal fun A _ _ Kb Sb => Sb ⊓ Kb = ⊥ ∧ IsCyclic ↥Sb

theorem kgStep6_of_cases (h6n : KGStep6Noncyc) (h6c : KGStep6Cyc) : KGStep6 := by
  intro G _ _ p P M x z hS hx hz H S hopt hO hΩ hnpc h2 L _ d3 hG hc hbot
  by_cases hcyc : IsCyclic ↥(KGC.img H (GLBPrimeCore p H) S)
  · exact h6c G p P M x z hS hx hz H S hopt hO hΩ hnpc h2 L d3 hG hc ⟨hbot, hcyc⟩
  · exact h6n _ p _ _ _ _ _ d3.toData.cfg hc hbot hcyc

theorem kgSteps56_of_cases (h2715 : KFact2715) (h5s : KGStep5Sylow) (h5p : KGStep5Para)
    (h6 : KGStep6) : KGSteps56 := by
  intro G _ _ p P M x z hS hx hz H S hopt hO hΩ hnpc h2 L _ d3 hG hc
  by_cases hbot : KGC.img H (GLBPrimeCore p H) S ⊓ KGC.img H (GLBPrimeCore p H) L = ⊥
  · exact h6 G p P M x z hS hx hz H S hopt hO hΩ hnpc h2 L d3 hG hc hbot
  · by_cases hsyl : CFSG.ABGLocalTools.IsSylowOf 2
        (KGC.img H (GLBPrimeCore p H) S ⊓ KGC.img H (GLBPrimeCore p H) L)
        (KGC.img H (GLBPrimeCore p H) L)
    · by_cases hB : fusionIsBenderGroup ↥(KGC.img H (GLBPrimeCore p H) L)
      · exact KGQ.false_of_bender_sylow d3.toData.cfg h2715 hsyl hB
      · exact h5s G p P M x z hS hx hz H S hopt hO hΩ hnpc h2 L d3 hG hc ⟨hbot, hsyl, hB⟩
    · exact h5p _ p _ _ _ _ _ d3.toData.cfg (d3.toData.strongEmb_img hG) hc hbot hsyl

theorem kgStep5Para_of_inputs (h131 : KFact131) (hpc : KFactParabolicCover) : KGStep5Para := by
  intro A _ _ p Kb Sb Bb Mb z c hse hconcl hne hns
  exact KGQ.false_of_not_sylow c hse hconcl.1 h131 hpc hne hns

theorem kgSteps56_of_inputs (h2715 : KFact2715) (h131 : KFact131) (hpc : KFactParabolicCover)
    (h5s : KGStep5Sylow) (h6n : KGStep6Noncyc) (h6c : KGStep6Cyc) : KGSteps56 :=
  kgSteps56_of_cases h2715 h5s (kgStep5Para_of_inputs h131 hpc) (kgStep6_of_cases h6n h6c)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
