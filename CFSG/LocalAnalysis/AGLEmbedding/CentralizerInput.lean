module

public import CFSG.LocalAnalysis.AGLEmbedding.CentralAlpha
public import CFSG.LocalAnalysis.AGLEmbedding.CentralAlphaOut
public import CFSG.LocalAnalysis.AGLEmbedding.CentralBeta
public import CFSG.LocalAnalysis.AGLEmbedding.CentralizerTransport
public import CFSG.LocalAnalysis.AGLEmbedding.RankOneAutomizer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.Assembly.LowTwoRank

structure D1CentralizerInput {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M : Subgroup G) (z : G) : Prop where
  ne_two : p ≠ 2
  sylow_le : (P : Subgroup G) ≤ M
  weakCore_le : GLBWeakCore p (P : Subgroup G) ≤ M
  four_le_pRank : 4 ≤ Open.pRank p (P : Subgroup G)
  orderOf_eq : orderOf z = p
  mem_centralizer : z ∈ Subgroup.centralizer (P : Set G)
  uniq : ∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ (P : Subgroup G) → orderOf y = p →
    y ∈ Subgroup.zpowers z
  not_le : ¬ Subgroup.centralizer ({z} : Set G) ≤ M
  core_le : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M
  iv : ∃ D : Subgroup G, D ≤ (P : Subgroup G) ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧ z ∈ D ∧
    Open.pRank p ((P : Subgroup G) ⊓ Subgroup.centralizer (D : Set G)) ≤ 2
  sl : ∃ E : Subgroup G, E ≤ (P : Subgroup G) ∧ Nat.card E = p ^ 3 ∧ (∀ x ∈ E, x ^ p = 1) ∧
    (Subgroup.center E).map E.subtype = Subgroup.zpowers z ∧
    ∃ e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p),
      StatedSL 2 (ZMod p) ≤ ((Subgroup.centralizer ({z} : Set G)).subgroupOf
        (Subgroup.normalizer (E : Set G))).map (centerQuotientAction E e)

theorem D1CentralizerInput.exists_reduced_centralizer_data {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : IsKProper G) {P : Sylow p G} {M : Subgroup G} {z : G}
    (h : D1CentralizerInput p P M z) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (Rbar : Sylow p X) (X₀ : Subgroup X) (zbar : X),
      ReducedNongeneration p X Rbar X₀ ∧ 4 ≤ Open.pRank p (Rbar : Subgroup X) ∧
      CatalogSimpleSections X ∧ zbar ∈ Subgroup.center X ∧ orderOf zbar = p ∧
      (∀ y ∈ (Rbar : Subgroup X), y ∈ Subgroup.centralizer (Rbar : Set X) → orderOf y = p →
        y ∈ Subgroup.zpowers zbar) ∧
      (∃ K : Subgroup X, IsComponentOf K ⊤ ∧ K.Normal) ∧
      (∃ v ∈ (Rbar : Subgroup X), orderOf v = p ∧
        Open.pRank p ((Rbar : Subgroup X) ⊓ Subgroup.centralizer ({v} : Set X)) ≤ 2) ∧
      ∃ E L : Subgroup X, E ≤ (Rbar : Subgroup X) ∧ Nat.card E = p ^ 3 ∧
        (∀ x ∈ E, x ^ p = 1) ∧ (Subgroup.center E).map E.subtype = Subgroup.zpowers zbar ∧
        ∃ e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p),
          StatedSL 2 (ZMod p) ≤
            (L.subgroupOf (Subgroup.normalizer (E : Set X))).map (centerQuotientAction E e) := by
  have hp : p.Prime := Fact.out
  obtain ⟨D, hDP, hD, hDcard, hzD, hDrank⟩ := h.iv
  obtain ⟨E, hEP, hEcard, hEexp, hEZ, e, hSL⟩ := h.sl
  obtain ⟨Pbar, hPbar, hred, hzbar⟩ := reducedNongeneration_centralizer_of_not_le hp h.ne_two P
    h.sylow_le h.weakCore_le (by have := h.four_le_pRank; omega) h.mem_centralizer h.orderOf_eq
    h.not_le h.core_le
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) p
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp h.mem_centralizer x hx)
  let zC : Subgroup.centralizer ({z} : Set G) :=
    ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨hzZ, hzbarp⟩ := hzbar zC rfl
  have hEC := hEP.trans hPC
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_mk _ hp hO (P.isPGroup'.to_le hEP) hEC
  obtain ⟨v, hvD, hvp, hvle⟩ :=
    exists_inf_centralizer_le hD hDcard hzD h.orderOf_eq h.mem_centralizer
  have hvP : v ∈ (P : Subgroup G) := hDP hvD
  have hPmap : ((P.subtype hPC : Sylow p _) : Subgroup _).map
      (Subgroup.centralizer ({z} : Set G)).subtype = P := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPC]
  have hlayer : CFSG.layer (Subgroup.centralizer ({z} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) ≠ ⊥ :=
    layer_ne_bot_of_four_le_pRank hp h.ne_two P h.sylow_le h.weakCore_le h.not_le
      (P.subtype hPC) hPmap.le (hPmap ▸ h.four_le_pRank) h.core_le
  refine ⟨_, inferInstance, inferInstance, Pbar, _, QuotientGroup.mk' _ zC, hred, ?_, ?_, hzZ,
    hzbarp, fun y hy hyc hyp => ?_, ?_, ⟨QuotientGroup.mk' _ ⟨v, hPC hvP⟩, ?_, ?_, ?_⟩,
    (E.subgroupOf _).map (QuotientGroup.mk' _),
    ((Subgroup.centralizer ({z} : Set G)).subgroupOf _).map (QuotientGroup.mk' _), ?_,
    (Nat.card_congr φ.toEquiv).symm.trans hEcard, ?_, map_center_eq_zpowers_mk _ hEC φ hφ hEZ, _,
    statedSL_le_map_mk _ hEC le_rfl φ hφ e hSL⟩
  · rw [hPbar, pRank_map_mk_eq_pRank_map_subtype hp _ hO, Subgroup.map_subgroupOf_eq_of_le hPC]
    exact h.four_le_pRank
  · have hz1 : z ≠ 1 := fun hz1 => hp.one_lt.ne (by rw [← h.orderOf_eq, hz1, orderOf_one])
    exact (catalogSimpleSections_of_isKProper hK _
      (centralizer_singleton_ne_top hs hnab hz1)).quotient _
  · refine mem_zpowers_mk_of_mem_centralizer _ hp hO P.isPGroup' hPC h.uniq (hPbar ▸ hy) ?_ hyp
    rw [← hPbar]
    exact hyc
  · obtain ⟨K, hK⟩ := exists_isComponentOf_of_layer_ne_bot hlayer
    exact ⟨K, hK, hred.normal_of_isComponentOf_of_center hzZ hzbarp hK⟩
  · rw [hPbar]
    exact ⟨⟨v, hPC hvP⟩, hvP, rfl⟩
  · exact orderOf_mk_of_coprime hp _ hO ((Subgroup.orderOf_coe _).symm.trans hvp)
  · rw [hPbar]
    exact (pRank_map_inf_centralizer_le _ hp hO P.isPGroup' hPC hvP).trans
      ((PreuniquenessRankFour.Helpers.pRank_mono p hp hvle).trans hDrank)
  · rw [hPbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hEP)
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow]
    exact (congrArg _ (Subtype.ext (hEexp c hc))).trans (map_one _)

theorem false_of_centralizerInput (hβ : KFactBeta) (hα : KFactAlpha) {G : Type} [Group G]
    [Finite G] (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hK : IsKProper G)
    {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {z : G}
    (h : D1CentralizerInput p P M z) : False := by
  obtain ⟨X, _, _, Rbar, X₀, zbar, hred, hR4, hX, hz, hzp, hzR, ⟨K, hK, hKn⟩,
    ⟨v, hvR, hvp, hv⟩, E, L, hER, hEcard, hEexp, hEZ, e, hSL⟩ :=
    h.exists_reduced_centralizer_data hs hnab hK
  by_cases hzK : zbar ∈ K
  · obtain ⟨hC, hout, he⟩ := hred.outTwo_of_mem hR4 hX hz hzp hK hKn hzK hα
    exact false_of_outTwo hred.prime hred.ne_two Rbar hR4 (mem_sylow_of_mem_center hz hzp Rbar)
      hzK hzp hzR hC hout hvR hvp hv he
  · obtain ⟨hZK, hcyc, hfacts⟩ := hred.rankOneLieAutFacts_of_not_mem hR4 hX hz hzp hK hKn hzK hβ
    exact false_of_rankOneLieAutFacts hred.ne_two hZK hfacts hEcard hEexp
      (inf_centralizer_eq_center_map_of_isCyclic hER hEexp hEZ hz hzp hcyc) e hSL

theorem D1Extremal.centralizerInput_of_hasPrimeConstraint {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} (hloc : D1Local p P M)
    {H R : Subgroup G} (h : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p) :
    ∃ z : G, D1CentralizerInput p P M z := by
  obtain ⟨z, -, hzp, hzc, huniq, hCM, hcoreM, -, -,
    ⟨D, hDR, hD, hDcard, hzD, -, hDrank⟩, E, hER, hEcard, hEexp, hEZ, e, hSL⟩ :=
    h.exists_sl_two_of_hasPrimeConstraint hloc hcon
  exact ⟨z, h.ne_two, h.sylow_le, h.weakCore_le,
    betaFour_all_sylows_rank_ge_four hloc.beta P, hzp, hzc, huniq, hCM, hcoreM,
    ⟨D, hDR.trans h.le_P, hD, hDcard, hzD, hDrank⟩,
    ⟨E, hER.trans h.le_P, hEcard, hEexp, hEZ, e,
      hSL.trans (Subgroup.map_mono fun x hx =>
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).2)⟩⟩

end CFSG.AGLEmbedding
