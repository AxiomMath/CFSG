module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamiliesAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KlingenRoute

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

namespace D1ComponentConfig

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem isPGroup_center (hcfg : D1ComponentConfig p P M H R Rbar) (hK : IsComponentOf K ⊤) :
    IsPGroup p (Subgroup.center K) :=
  isPGroup_center_of_isComponentOf hcfg.red.prime hcfg.red.core_eq_bot hK

theorem simple_catalog_center_quotient (hcfg : D1ComponentConfig p P M H R Rbar)
    (hK : IsComponentOf K ⊤) :
    IsSimpleGroup (K ⧸ Subgroup.center K) ∧ (∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a) ∧
      IsCatalogGroup (K ⧸ Subgroup.center K) :=
  ⟨hK.2.2.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2,
    hcfg.catalog.isCatalogGroup_center_quotient hK⟩

theorem mem_of_mem_centralizer (hcfg : D1ComponentConfig p P M H R Rbar)
    (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) :
    ∀ c ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)), orderOf c = p →
      c ∈ K := by
  have : Fact p.Prime := ⟨hcfg.red.prime⟩
  exact fun c hc hcp => mem_of_mem_centralizer_of_orderOf_eq Rbar
    (normal_of_forall_isComponentOf_eq hK huniq)
    (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp

theorem mem_center_of_mem_centralizer (hcfg : D1ComponentConfig p P M H R Rbar)
    (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) :
    ∀ c ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype := fun c hc hcp =>
  mem_map_center_of_mem_of_mem_centralizer (hcfg.mem_of_mem_centralizer hK huniq hcent c hc hcp) hc

theorem isPGroup_centralizer (hcfg : D1ComponentConfig p P M H R Rbar) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) :
    IsPGroup p (Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) :=
  isPGroup_centralizer_of_forall_mem hcfg.red.prime hcfg.red.ne_two hcfg.red.core_eq_bot
    (normal_of_forall_isComponentOf_eq hK huniq) (hcfg.mem_of_mem_centralizer hK huniq hcent)

theorem isCyclic_centralizer (hcfg : D1ComponentConfig p P M H R Rbar) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) :
    IsCyclic (Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) :=
  isCyclic_centralizer_of_forall_mem hcfg.red.prime hcfg.red.ne_two hcfg.red.core_eq_bot
    (normal_of_forall_isComponentOf_eq hK huniq) (hcfg.mem_of_mem_centralizer hK huniq hcent)
    (hcfg.red.isCyclic_map_center hK (normal_of_forall_isComponentOf_eq hK huniq))

theorem centralizer_eq_bot (hcfg : D1ComponentConfig p P M H R Rbar) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    (hZ : Subgroup.center K = ⊥) :
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ :=
  centralizer_eq_bot_of_forall_mem hcfg.red.prime hcfg.red.ne_two hcfg.red.core_eq_bot
    (normal_of_forall_isComponentOf_eq hK huniq) (hcfg.mem_of_mem_centralizer hK huniq hcent) hZ

end D1ComponentConfig

@[expose] def D1CaseThreeAlt : Prop :=
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
      ∀ n : ℕ, 5 ≤ n → Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) → False

@[expose] def D1CaseThreeLie : Prop :=
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
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) → False

@[expose] def D1CaseThreeSpor : Prop :=
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
      ∀ s : TauCeti.SporadicName,
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) → False

theorem d1CaseThreeNotKlingen_of_families (ha : D1CaseThreeAlt) (hl : D1CaseThreeLie)
    (hs : D1CaseThreeSpor) : D1CaseThreeNotKlingen := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD
  obtain ⟨-, hnonab, i, ⟨e⟩⟩ := hcfg.simple_catalog_center_quotient hK
  cases i with
  | cyclic q hq => exact (not_nonempty_mulEquiv_zmod hnonab ⟨e⟩).elim
  | alternating n hn => exact ha G p P M H R Rbar hcfg K hK huniq hnc hcent hKD n hn ⟨e⟩
  | lie d => exact hl G p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨e⟩
  | sporadic s => exact hs G p P M H R Rbar hcfg K hK huniq hnc hcent hKD s ⟨e⟩

end CFSG.AGLEmbedding
