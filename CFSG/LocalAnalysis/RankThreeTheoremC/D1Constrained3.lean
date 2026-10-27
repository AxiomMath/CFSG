module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSL
public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding (D1Extremal D1Escape glbPrimeCore_le glbPrimeCore_normal glbPrimeCore_coprime
  centerQuotientAction)

variable {G : Type} [Group G] [Finite G]

theorem exists_isolated_vertex3 {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p) :
    ∃ z : G, ∃ D : Subgroup G, D ≤ R ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧ z ∈ D ∧
      ¬ Subgroup.normalizer (D : Set G) ≤ M ∧
      Open.pRank p ((P : Subgroup G) ⊓ Subgroup.centralizer (D : Set G)) ≤ 2 ∧
      orderOf z = p ∧ z ∈ Subgroup.centralizer (P : Set G) ∧
      (∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ (P : Subgroup G) → orderOf y = p →
        y ∈ Subgroup.zpowers z) ∧
      ¬ Subgroup.centralizer ({z} : Set G) ≤ M ∧
      GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M ∧
      (R ≠ (P : Subgroup G) →
        Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))))) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hP3 : 3 ≤ Open.pRank p (P : Subgroup G) :=
    h.three_le_pRank.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp h.le_P)
  obtain ⟨D, hDR, hD, hDcard, hDN⟩ := h.toD1Escape.exists_isElemAbelian_normalizer_not_le hcon
  obtain ⟨z, hzD, hzp, hzc, huniq⟩ := CFSG.AGLEmbedding.exists_mem_center_of_normalizer_not_le
    hp h.ne_two P h.sylow_le h.weakCore_le hP3 hD hDcard (hDR.trans h.le_P) hDN
  have hzR := hDR hzD
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc x hx)
  have hCM := h.toD1Escape.centralizer_not_le_of_hasPrimeConstraint hcon hP3 hzR hzc hzp
  have hcoreM : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M :=
    intersecting_local_primeCore_le p hp P h.sylow_le h.weakCore_le
      (hP3.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf hPC h.sylow_le)))
  refine ⟨z, D, hDR, hD, hDcard, hzD, hDN,
    CFSG.AGLEmbedding.pRank_inf_centralizer_le_two_of_normalizer_not_le hp P h.sylow_le
      h.weakCore_le hD hDcard (hDR.trans h.le_P) hDN, hzp, hzc, huniq, hCM, hcoreM,
    fun hRP => ?_⟩
  exact CFSG.AGLEmbedding.odd_card_of_twoLocals_le hp P.isPGroup' hPC hCM
    (glbPrimeCore_le p _) (glbPrimeCore_normal p _) (glbPrimeCore_coprime p _) hcoreM
    fun T hT hT1 hPT => h.normalizer_le_of_sylow_le hRP hT hT1 hPT

structure D1CentralizerInput3 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M : Subgroup G) (z : G) : Prop where
  ne_two : p ≠ 2
  sylow_le : (P : Subgroup G) ≤ M
  weakCore_le : GLBWeakCore p (P : Subgroup G) ≤ M
  pRank_eq : Open.pRank p (P : Subgroup G) = 3
  orderOf_eq : orderOf z = p
  mem_centralizer : z ∈ Subgroup.centralizer (P : Set G)
  uniq : ∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ (P : Subgroup G) → orderOf y = p →
    y ∈ Subgroup.zpowers z
  not_le : ¬ Subgroup.centralizer ({z} : Set G) ≤ M
  core_le : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M
  iv : ∃ D : Subgroup G, D ≤ (P : Subgroup G) ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧
    z ∈ D ∧ Open.pRank p ((P : Subgroup G) ⊓ Subgroup.centralizer (D : Set G)) ≤ 2
  sl : ∃ E : Subgroup G, E ≤ (P : Subgroup G) ∧ Nat.card E = p ^ 3 ∧ (∀ x ∈ E, x ^ p = 1) ∧
    (Subgroup.center E).map E.subtype = Subgroup.zpowers z ∧
    ∃ e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p),
      StatedSL 2 (ZMod p) ≤ ((Subgroup.centralizer ({z} : Set G)).subgroupOf
        (Subgroup.normalizer (E : Set G))).map (centerQuotientAction E e)

@[expose] def D1CentralizerSylowCase3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
    IsCoreMaxLocal p P M → ∀ H R : Subgroup G, D1Extremal p P M H R → R = (P : Subgroup G) →
      ∀ (_ : Fact p.Prime) (z : G), D1CentralizerInput3 p P M z → False

@[expose] def D1CentralizerComponentCase3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
    IsCoreMaxLocal p P M → ∀ H R : Subgroup G, D1Extremal p P M H R → R ≠ (P : Subgroup G) →
      ∀ (_ : Fact p.Prime) (z : G), D1CentralizerInput3 p P M z →
      Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) →
      CFSG.layer (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) ≠ ⊥ → False

@[expose] def D1CentralizerConstrainedCase3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
    IsCoreMaxLocal p P M → ∀ H R : Subgroup G, D1Extremal p P M H R → R ≠ (P : Subgroup G) →
      ∀ (_ : Fact p.Prime) (z : G), D1CentralizerInput3 p P M z →
      Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) →
      CFSG.layer (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) = ⊥ → False

end CFSG.LocalAnalysis.RankThreeTheoremC
