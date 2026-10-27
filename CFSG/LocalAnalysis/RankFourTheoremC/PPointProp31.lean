module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExclude

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

structure PPointFacts (p : ℕ) (M : Subgroup G) (x : G) (R : Sylow p (RedCent p x))
    (K : Subgroup (RedCent p x)) (i : TauCeti.CFSGIndex) : Prop where
  red : PPointReduced p M x R K
  center_eq_bot : center K = ⊥
  isPGroup : IsPGroup p (centralizer (K : Set (RedCent p x)))
  isCyclic : IsCyclic (centralizer (K : Set (RedCent p x)))
  equiv : Nonempty (K ≃* i.Group)
  type : PPointType p i
  inner : GL83OuterType24 p i ∨ ∀ g ∈ (R : Subgroup (RedCent p x)), g ^ p = 1 →
    g ∈ K ⊔ centralizer (K : Set (RedCent p x))

@[expose] def PPointExclusionFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D1Global G → D1For G → FullCoreLocality G →
    ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M : Subgroup G), D1Local p P M → 5 ≤ p →
      ∀ x : G, IsPPoint p P M x → ∀ (R : Sylow p (RedCent p x)) (K : Subgroup (RedCent p x)),
        PPointReduced p M x R K → ∀ i : TauCeti.CFSGIndex, Nonempty (K ≃* i.Group) →
          PPointExcluded p i → False

namespace IsPPoint

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem exists_pPointFacts [Fact p.Prime] (hp2 : p ≠ 2) (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hexcl : 5 ≤ p → PPointExclusionFive)
    (hUB : KFactUnitaryBorelMaximal) (hUI : KFactUnitaryInvolution)
    (hRB : KFactReeBorelMaximal) (hRI : KFactReeInvolution) (hS : D1Global G) (hD1 : D1For G)
    (hFC : FullCoreLocality G) (hloc : D1Local p P M) (h : IsPPoint p P M x) :
    ∃ (R : Sylow p (RedCent p x)) (K : Subgroup (RedCent p x)) (i : TauCeti.CFSGIndex),
      PPointFacts p M x R K i ∧ (R : Subgroup (RedCent p x)) =
        (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨R, K, hRK, hReq⟩ := h.exists_pPointReduced hFC hloc
  obtain ⟨hzc, hzp⟩ := h.central_xbar hloc
  have hcat := h.catalogSimpleSections hS hp
  obtain ⟨i, ⟨e⟩, hi, hio⟩ := hRK.exists_equiv_type hp2 h243 h244 hcat hzc hzp
  refine ⟨R, K, i, ⟨hRK, hRK.center_eq_bot hp2 h243 hcat, hRK.isPGroup_centralizer hzc hzp,
    hRK.isCyclic_centralizer hzc hzp, ⟨e⟩, ?_, hio⟩, hReq⟩
  rcases hi.cases hp with hty | hex
  · exact hty
  · exfalso
    by_cases hp3 : p = 3
    · subst hp3
      exact hRK.false_of_excluded_three h243 hUB hUI hRB hRI hS hD1 hloc h hex ⟨e⟩
    · have hp5 : 5 ≤ p := by
        by_contra hlt
        interval_cases p <;> first | omega | (revert hp; norm_num)
      exact hexcl hp5 G hS hD1 hFC p P M hloc hp5 x h R K hRK i ⟨e⟩ hex

theorem exists_pPointFacts_three {P : Sylow 3 G} (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hUB : KFactUnitaryBorelMaximal)
    (hUI : KFactUnitaryInvolution) (hRB : KFactReeBorelMaximal) (hRI : KFactReeInvolution)
    (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G) (hloc : D1Local 3 P M)
    (h : IsPPoint 3 P M x) :
    ∃ (R : Sylow 3 (RedCent 3 x)) (K : Subgroup (RedCent 3 x)) (i : TauCeti.CFSGIndex),
      PPointFacts 3 M x R K i ∧ (R : Subgroup (RedCent 3 x)) =
        (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exists_pPointFacts (by norm_num) h243 h244 (fun h5 => absurd h5 (by norm_num)) hUB hUI hRB hRI
    hS hD1 hFC hloc h

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC
