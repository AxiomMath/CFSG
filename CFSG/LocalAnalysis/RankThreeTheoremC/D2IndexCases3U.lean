module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PrimeThree3Leaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporNarrow3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

@[expose] def D2IndexCaseAt3U (G : Type) [Group G] [Finite G] (i : TauCeti.CFSGIndex)
    (Pp : ℕ → Prop) : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ p ∈ rankThreeSigmaA G, Pp p → ∀ (P : Sylow p G) (A H R : Subgroup G),
    IsCoreMaxLocal p P M → D2Escape p P M A H R →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* i.Group) → False

@[expose] def D2IndexCase3U (G : Type) [Group G] [Finite G] (i : TauCeti.CFSGIndex) : Prop :=
  D2IndexCaseAt3U G i fun _ => True

@[expose] def D2IndexCaseStrongAt3U (G : Type) [Group G] [Finite G] (i : TauCeti.CFSGIndex)
    (Pp : ℕ → Prop) : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ p ∈ rankThreeSigmaA G, Pp p → ∀ (P : Sylow p G) (A H R : Subgroup G),
    IsCoreMaxLocal p P M → D2Escape p P M A H R →
    rankThreeGamma 1 p (P : Subgroup G) ≤ M →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* i.Group) → False

theorem d2IndexCaseAt3U_of_pair {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (hPp : ∀ p, Pp p → p = 3) (hpair : D2PairAt i Pp) (h84 : Asc81bEightFour)
    (hX : D1NoXBlock3 G) (h : D2IndexCaseStrongAt3U G i Pp) : D2IndexCaseAt3U G i Pp := by
  intro hSet hD1 M hM ha hb p hp hpp P A H R hMP hesc Rbar K hRbar hK he
  obtain rfl := hPp p hpp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpr : AGLPair 3 M H R := hesc.toPair (aglGlobal_of_setting hSet)
    (hesc.twoCore_inf_eq_of_primeCore_inf_eq
      (hesc.primeCore_inf_eq_iff.mpr (hpair _ 3 hpp Rbar _ _ K hK he)))
  have hns : ¬ Group.IsSolvable M := fun hsolv =>
    hpr.false_of_isSolvable h84 (noXBlockFor_of_setting hX hSet) hsolv
  exact h hSet hD1 M hM ha hb 3 hp hpp P A H R hMP hesc ((hb hp P hMP).2 hns) Rbar K hRbar
    hK he

theorem d2IndexCaseAt3U_of_vacuous {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : ∀ p, Pp p → D2VacuousAt i p) : D2IndexCaseAt3U G i Pp := by
  intro hS hD1 M hM ha hb p hp hpp P A H R hMP hesc Rbar K hRbar hK he
  exact h p hpp _ Rbar _ _ K hK he

theorem d2IndexCaseAt3U_of_indexCase3U {i : TauCeti.CFSGIndex} (h : D2IndexCase3U G i)
    (Pp : ℕ → Prop) : D2IndexCaseAt3U G i Pp :=
  fun hS hD1 M hM ha hb p hp _ => h hS hD1 M hM ha hb p hp trivial

theorem d2IndexCaseAt3U_of_vac_cases {i : TauCeti.CFSGIndex} {Pp ZK : ℕ → Prop}
    (hZK : ∀ p, ZK p → D2VacuousAt i p)
    (h : D2IndexCaseAt3U G i fun p => Pp p ∧ ¬ ZK p) : D2IndexCaseAt3U G i Pp := by
  intro hS hD1 M hM ha hb p hp hpp P A H R hMP hesc Rbar K hRbar hK he
  by_cases hr : ZK p
  · exact hZK p hr _ Rbar _ _ K hK he
  · exact h hS hD1 M hM ha hb p hp ⟨hpp, hr⟩ P A H R hMP hesc Rbar K hRbar hK he

theorem d2IndexCase3U_sporadic_of_section (hsec : SporSectionFacts3) {s : TauCeti.SporadicName}
    (hs : s ∈ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName)) :
    D2IndexCase3U G (.sporadic s) := by
  intro hS hD1 M hM ha hb p hp _ P A H R hMP hesc Rbar K hRbar hK ⟨e⟩
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.component.2.2.2
  have hnonab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
      hK.component.2.2
  have e' : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hK.center_eq_bot).trans QuotientGroup.quotientBot).trans e
  exact false_of_mem_sectionExcluded3 hsec hS.rank (primeComplementCore (G := H) p) hsimple hnonab
    hs e'

@[expose] def D2U3ThreeStrong3U (G : Type) [Group G] [Finite G] : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
    D2IndexCaseStrongAt3U G (.lie d) fun p => p = d.1.characteristic ∧ p = 3

@[expose] def D2U3Three3U (G : Type) [Group G] [Finite G] : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
    D2IndexCaseAt3U G (.lie d) fun p => p = d.1.characteristic ∧ p = 3

@[expose] def D2AltSixStrong3U (G : Type) [Group G] [Finite G] : Prop :=
  D2IndexCaseStrongAt3U G (.alternating 6 (by norm_num)) fun p => p = 3

@[expose] def D2AltSixCase3U (G : Type) [Group G] [Finite G] : Prop :=
  D2IndexCaseAt3U G (.alternating 6 (by norm_num)) fun p => p = 3

theorem d2U3Three3U_of_strong (h84 : Asc81bEightFour) (hX : D1NoXBlock3 G)
    (h : D2U3ThreeStrong3U G) : D2U3Three3U G :=
  fun d hd => d2IndexCaseAt3U_of_pair (fun _ hp => hp.2) (d2PairAt_u3 hd) h84 hX (h d hd)

theorem d2AltSixCase3U_of_strong (h84 : Asc81bEightFour) (hX : D1NoXBlock3 G)
    (h : D2AltSixStrong3U G) : D2AltSixCase3U G :=
  d2IndexCaseAt3U_of_pair (fun _ hp => hp) d2PairAt_altSix h84 hX h

end CFSG.LocalAnalysis.RankThreeTheoremC
