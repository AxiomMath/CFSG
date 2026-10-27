module

public import CFSG.LocalAnalysis.AGLEmbedding.KlingenRouteAux
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentTrichotomy
public import CFSG.LocalAnalysis.AGLEmbedding.CentralizerInput

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.Assembly.LowTwoRank

@[expose] def HasKlingenData {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    (Rbar : Sylow p X) (X₀ : Subgroup X) : Prop :=
  ∃ E D L : Subgroup X, E ≤ (Rbar : Subgroup X) ∧ Nat.card E = p ^ 3 ∧ (∀ x ∈ E, x ^ p = 1) ∧
    Nat.card (Subgroup.center E) = p ∧ D ≤ E ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧
    (∀ y ∈ D, y ∈ Subgroup.centralizer (Rbar : Set X) →
      y ∈ (Subgroup.center E).map E.subtype) ∧
    ¬ Subgroup.normalizer (D : Set X) ≤ X₀ ∧
    L ≤ Subgroup.centralizer (((Subgroup.center E).map E.subtype : Subgroup X) : Set X) ∧
    ¬ L ≤ X₀ ∧
    ∃ e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p),
      StatedSL 2 (ZMod p) ≤ (L.subgroupOf (Subgroup.normalizer (E : Set X))).map
        (centerQuotientAction E e)

structure D1CentralizerInputCore {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M : Subgroup G) (z : G) : Prop where
  ne_two : p ≠ 2
  sylow_le : (P : Subgroup G) ≤ M
  weakCore_le : GLBWeakCore p (P : Subgroup G) ≤ M
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

theorem D1CentralizerInputCore.toInput {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {M : Subgroup G} {z : G} (h : D1CentralizerInputCore p P M z)
    (h4 : 4 ≤ Open.pRank p (P : Subgroup G)) : D1CentralizerInput p P M z :=
  ⟨h.ne_two, h.sylow_le, h.weakCore_le, h4, h.orderOf_eq, h.mem_centralizer, h.uniq, h.not_le,
    h.core_le, h.iv, h.sl⟩

theorem D1Escape.centralizerInputCore_of_klingen {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {H R : Subgroup G}
    (h : D1Escape p P M H R)
    (hP3 : 3 ≤ Open.pRank p (P : Subgroup G)) (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (hRbar : (Rbar : Subgroup _) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : HasKlingenData p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))) :
    ∃ z : G, D1CentralizerInputCore p P M z := by
  have hp : p.Prime := Fact.out
  set O := primeComplementCore (G := H) p
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hR : IsPGroup p R := h.isPGroup
  obtain ⟨Eb, Db, L, hEbR, hEbcard, hEbexp, hEbZ, hDbE, hDb, hDbcard, hDbC, hDbN, hLC,
    hLX₀, eb, hSL⟩ := hK
  obtain ⟨D, hDH, hDR, hDmap, -, ψD, hψD⟩ :=
    exists_lift_of_le_map hp h.le_H hR O hO ((hDbE.trans hEbR).trans hRbar.le)
  have hD : IsElemAbelian p D := isElemAbelian_of_mulEquiv ψD hDb
  have hDcard : Nat.card D = p ^ 2 := (Nat.card_congr ψD.toEquiv).trans hDbcard
  have hDN : ¬ Subgroup.normalizer (D : Set G) ≤ M := by
    obtain ⟨x, hxN, hxX₀⟩ := Set.not_subset.mp hDbN
    obtain ⟨g, hgN, rfl⟩ := exists_mem_normalizer_mk_eq_of_mem_normalizer hp O hO
      (hR.to_le hDR).comap_subtype (hDmap ▸ hxN)
    have hgD : (g : G) ∈ Subgroup.normalizer (D : Set G) := by
      have hg : (g : G) ∈ Subgroup.normalizer
          (((D.subgroupOf H).map H.subtype : Subgroup G) : Set G) :=
        Subgroup.le_normalizer_map H.subtype ⟨g, hgN, rfl⟩
      rwa [Subgroup.map_subgroupOf_eq_of_le hDH] at hg
    exact fun hle => hxX₀ ⟨g, ⟨g.2, hle hgD⟩, rfl⟩
  obtain ⟨z, hzD, hzp, hzc, huniq⟩ := exists_mem_center_of_normalizer_not_le hp h.ne_two P
    h.sylow_le h.weakCore_le hP3 hD hDcard (hDR.trans h.le_P) hDN
  set zH : H := ⟨z, hDH hzD⟩
  have hzR : z ∈ R := hDR hzD
  have hzHp : orderOf zH = p := (Subgroup.orderOf_mk z _).trans hzp
  have hzbarD : QuotientGroup.mk' O zH ∈ Db := by
    have hz := (ψD ⟨z, hzD⟩).2
    rwa [hψD] at hz
  have hzbarC : QuotientGroup.mk' O zH ∈ Subgroup.centralizer (Rbar : Set (H ⧸ O)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : r ∈ (Rbar : Subgroup (H ⧸ O)) := hr
    rw [hRbar] at hr'
    obtain ⟨t, ht, rfl⟩ := hr'
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc t (h.le_P ht)))
  have hzbarZ := hDbC _ hzbarD hzbarC
  have hDrank := pRank_inf_centralizer_le_two_of_normalizer_not_le hp P h.sylow_le
    h.weakCore_le hD hDcard (hDR.trans h.le_P) hDN
  have hCM : ¬ Subgroup.centralizer ({z} : Set G) ≤ M := by
    obtain ⟨ℓ, hℓL, hℓX₀⟩ := Set.not_subset.mp hLX₀
    have hcomm : QuotientGroup.mk' O zH * ℓ = ℓ * QuotientGroup.mk' O zH :=
      Subgroup.mem_centralizer_iff.mp (hLC hℓL) _ hzbarZ
    have hzpow : IsPGroup p (Subgroup.zpowers zH) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzHp, pow_one])
    have hℓN : ℓ ∈ Subgroup.normalizer (((Subgroup.zpowers zH).map (QuotientGroup.mk' O) :
        Subgroup (H ⧸ O)) : Set (H ⧸ O)) := by
      rw [MonoidHom.map_zpowers]
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.zpow_left hcomm k).eq
    obtain ⟨g, -, rfl, hgz⟩ := exists_mem_normalizer_mk_eq_commute hp O hO hzpow hℓN
      (Subgroup.mem_zpowers zH) hcomm.symm
    have hgC : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hgz)
    exact fun hle => hℓX₀ ⟨g, ⟨g.2, hle hgC⟩, rfl⟩
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc x hx)
  have hcoreM : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M :=
    intersecting_local_primeCore_le p hp P h.sylow_le h.weakCore_le
      (hP3.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp (_root_.le_inf hPC h.sylow_le)))
  obtain ⟨E, hEH, hER, hEmap, hEmem, ψE, hψE⟩ :=
    exists_lift_of_le_map hp h.le_H hR O hO (hEbR.trans hRbar.le)
  have hEp : IsPGroup p (E.subgroupOf H) := (hR.to_le hER).comap_subtype
  have hzE : z ∈ E := hEmem zH hzR (Subgroup.map_subtype_le _ hzbarZ)
  have hEZ : (Subgroup.center E).map E.subtype = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨z, hzE⟩, Subgroup.mem_center_iff.mpr fun v => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hzc v (h.le_P (hER v.2))
    · rw [Subgroup.card_map_of_injective E.subtype_injective, Nat.card_zpowers, hzp,
        Nat.card_congr (Subgroup.centerCongr ψE).toEquiv, hEbZ]
  have hlift : ∀ x ∈ L, x ∈ Subgroup.normalizer (Eb : Set (H ⧸ O)) →
      ∃ g' ∈ Subgroup.centralizer ({z} : Set G), g' ∈ Subgroup.normalizer (E : Set G) ∧
        ∀ u v : Eb, (v : H ⧸ O) = x * u * x⁻¹ →
          ((ψE.symm v : E) : G) = g' * ψE.symm u * g'⁻¹ := by
    intro x hxL hxN
    have hcomm : x * QuotientGroup.mk' O zH = QuotientGroup.mk' O zH * x :=
      (Subgroup.mem_centralizer_iff.mp (hLC hxL) _ hzbarZ).symm
    obtain ⟨g, hgN, rfl, hgz⟩ := exists_mem_normalizer_mk_eq_commute hp O hO hEp
      (hEmap ▸ hxN) (show zH ∈ E.subgroupOf H from hzE) hcomm
    have hgE : (g : G) ∈ Subgroup.normalizer (E : Set G) := by
      have hg : (g : G) ∈ Subgroup.normalizer
          (((E.subgroupOf H).map H.subtype : Subgroup G) : Set G) :=
        Subgroup.le_normalizer_map H.subtype ⟨g, hgN, rfl⟩
      rwa [Subgroup.map_subgroupOf_eq_of_le hEH] at hg
    refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hgz), hgE,
      fun u v huv => ?_⟩
    have hc : (g : G) * (ψE.symm u : G) * (g : G)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp hgE _).mp (ψE.symm u).2
    have key : ψE ⟨_, hc⟩ = v := by
      apply Subtype.ext
      have h1 : (Subgroup.inclusion hEH ⟨_, hc⟩ : H) =
          g * Subgroup.inclusion hEH (ψE.symm u) * g⁻¹ := Subtype.ext rfl
      rw [hψE, h1, map_mul, map_mul, map_inv, ← hψE, MulEquiv.apply_symm_apply, huv]
    rw [← key, MulEquiv.symm_apply_apply]
  exact ⟨z, h.ne_two, h.sylow_le, h.weakCore_le, hzp, hzc, huniq, hCM, hcoreM,
    ⟨D, hDR.trans h.le_P, hD, hDcard, hzD, hDrank⟩,
    ⟨E, hER.trans h.le_P, (Nat.card_congr ψE.toEquiv).trans hEbcard,
      pow_eq_one_of_mulEquiv ψE hEbexp, hEZ, _,
      statedSL_le_map_centerQuotientAction_of_mulEquiv ψE.symm eb hSL hlift⟩⟩

theorem D1Escape.centralizerInput_of_klingen {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} (hloc : D1Local p P M) {H R : Subgroup G}
    (h : D1Escape p P M H R) (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (hRbar : (Rbar : Subgroup _) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : HasKlingenData p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))) :
    ∃ z : G, D1CentralizerInput p P M z := by
  have hP4 : 4 ≤ Open.pRank p (P : Subgroup G) := betaFour_all_sylows_rank_ge_four hloc.beta P
  obtain ⟨z, hz⟩ := h.centralizerInputCore_of_klingen (by omega) Rbar hRbar hK
  exact ⟨z, hz.toInput hP4⟩

theorem D1Extremal.centralizerInput_of_klingen {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} (hloc : D1Local p P M) {H R : Subgroup G}
    (h : D1Extremal p P M H R) (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (hRbar : (Rbar : Subgroup _) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : HasKlingenData p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))) :
    ∃ z : G, D1CentralizerInput p P M z :=
  h.toD1Escape.centralizerInput_of_klingen hloc Rbar hRbar hK

@[expose] def D1CaseThreeNotKlingen : Prop :=
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
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) → False

theorem d1CaseThree_of_notKlingen (hβ : KFactBeta) (hα : KFactAlpha)
    (h : D1CaseThreeNotKlingen) : D1CaseThree := by
  intro G _ _ p P M H R Rbar hcfg K hK huniq hnc hcent
  have : Fact p.Prime := ⟨hcfg.ext.prime⟩
  by_cases hKD : HasKlingenData p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
  · obtain ⟨z, hz⟩ := hcfg.ext.centralizerInput_of_klingen hcfg.loc Rbar hcfg.rbar hKD
    exact false_of_centralizerInput hβ hα hcfg.glob.simple hcfg.glob.nonab hcfg.glob.kProper hz
  · exact h G p P M H R Rbar hcfg K hK huniq hnc hcent hKD

end CFSG.AGLEmbedding
