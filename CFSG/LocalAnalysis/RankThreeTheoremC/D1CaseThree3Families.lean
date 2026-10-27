module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKill
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylowAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.AGLEmbedding (CaseThreeKFact HasKlingenData ReducedNongeneration
  center_le_commutator_of_isPerfect le_inf_sup_centralizer le_of_weakCore_eq_top
  mem_sup_centralizer_of_pow normal_of_forall_isComponentOf_eq not_dvd_card_outer_of_quotient
  not_le_of_le_sup_centralizer not_nonempty_mulEquiv_zmod pRank_le_two_of_centralizer_eq_bot
  weakCore_le_comap)

variable {G : Type} [Group G] [Finite G]

namespace D1ComponentConfig3

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem isPGroup_center (hcfg : D1ComponentConfig3 p P M H R Rbar) (hK : IsComponentOf K ⊤) :
    IsPGroup p (Subgroup.center K) :=
  CFSG.AGLEmbedding.isPGroup_center_of_isComponentOf hcfg.red.prime hcfg.red.core_eq_bot hK

theorem simple_catalog_center_quotient (hcfg : D1ComponentConfig3 p P M H R Rbar)
    (hK : IsComponentOf K ⊤) :
    IsSimpleGroup (K ⧸ Subgroup.center K) ∧ (∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a) ∧
      IsCatalogGroup (K ⧸ Subgroup.center K) :=
  ⟨hK.2.2.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2,
    hcfg.catalog.isCatalogGroup_center_quotient hK⟩

theorem mem_of_mem_centralizer (hcfg : D1ComponentConfig3 p P M H R Rbar)
    (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) :
    ∀ c ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)), orderOf c = p →
      c ∈ K := by
  have : Fact p.Prime := ⟨hcfg.red.prime⟩
  exact fun c hc hcp => CFSG.AGLEmbedding.mem_of_mem_centralizer_of_orderOf_eq Rbar
    (normal_of_forall_isComponentOf_eq hK huniq)
    (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp

theorem isPGroup_centralizer (hcfg : D1ComponentConfig3 p P M H R Rbar) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) :
    IsPGroup p (Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) :=
  CFSG.AGLEmbedding.isPGroup_centralizer_of_forall_mem hcfg.red.prime hcfg.red.ne_two
    hcfg.red.core_eq_bot (normal_of_forall_isComponentOf_eq hK huniq)
    (hcfg.mem_of_mem_centralizer hK huniq hcent)

theorem isCyclic_center (hcfg : D1ComponentConfig3 p P M H R Rbar) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) :
    IsCyclic (Subgroup.center K) := by
  have h := hcfg.red.isCyclic_map_center hK (normal_of_forall_isComponentOf_eq hK huniq)
  let e := Subgroup.equivMapOfInjective (Subgroup.center K) K.subtype K.subtype_injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem centralizer_eq_bot (hcfg : D1ComponentConfig3 p P M H R Rbar) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    (hZ : Subgroup.center K = ⊥) :
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ :=
  CFSG.AGLEmbedding.centralizer_eq_bot_of_forall_mem hcfg.red.prime hcfg.red.ne_two
    hcfg.red.core_eq_bot (normal_of_forall_isComponentOf_eq hK huniq)
    (hcfg.mem_of_mem_centralizer hK huniq hcent) hZ

end D1ComponentConfig3

@[expose] def D1CaseThreeAlt3 (G : Type) [Group G] [Finite G] : Prop :=
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
      ∀ n : ℕ, 5 ≤ n → Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) → False

@[expose] def D1CaseThreeLie3 (G : Type) [Group G] [Finite G] : Prop :=
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
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) → False

@[expose] def D1CaseThreeSpor3 (G : Type) [Group G] [Finite G] : Prop :=
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
      ∀ s : TauCeti.SporadicName,
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) → False

theorem d1CaseThreeNotKlingen3_of_families (ha : D1CaseThreeAlt3 G) (hl : D1CaseThreeLie3 G)
    (hs : D1CaseThreeSpor3 G) : D1CaseThreeNotKlingen3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD
  obtain ⟨-, hnonab, i, ⟨e⟩⟩ := hcfg.simple_catalog_center_quotient hK
  cases i with
  | cyclic q hq => exact (not_nonempty_mulEquiv_zmod hnonab ⟨e⟩).elim
  | alternating n hn => exact ha p P M H R Rbar hcfg K hK huniq hnc hcent hKD n hn ⟨e⟩
  | lie d => exact hl p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨e⟩
  | sporadic s => exact hs p P M H R Rbar hcfg K hK huniq hnc hcent hKD s ⟨e⟩

theorem false_of_caseThreeKFact3 {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hcfg : D1ComponentConfig3 p P M H R Rbar)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hnc : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    (hKD : ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))))
    [Finite (Outer K)] (hOut : ¬ p ∣ Nat.card (Outer K)) (hfact : CaseThreeKFact p K) : False :=
  CFSG.AGLEmbedding.false_of_caseThreeKFact_of_red hcfg.red hK huniq hnc hcent hKD hOut
    CFSG.AGLEmbedding.s2Lemma CFSG.AGLEmbedding.klingenTransport hfact

end CFSG.LocalAnalysis.RankThreeTheoremC
