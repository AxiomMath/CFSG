module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedEscape
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbits

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Center

variable {X : Type*} [Group X]

theorem exists_isComponentOf_of_layer_ne_bot (hE : CFSG.layer X ≠ ⊥) :
    ∃ K : Subgroup X, IsComponentOf K ⊤ := by
  by_contra! hno
  exact hE (sSup_eq_bot.mpr fun K hK => ((hno K) ((CFSG.isComponent_iff_open K).mp hK)).elim)

theorem mem_pCore_of_mem_center {p : ℕ} {z : X} (hz : z ∈ Subgroup.center X)
    (hzp : orderOf z = p) :
    z ∈ CFSG.pCore p X :=
  Subgroup.mem_sSup_of_mem (S := {K : Subgroup X | K.Normal ∧ IsPGroup p K})
    ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz),
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])⟩
    (Subgroup.mem_zpowers z)

theorem mem_sylow_of_mem_center {p : ℕ} {z : X} (hz : z ∈ Subgroup.center X)
    (hzp : orderOf z = p) (R : Sylow p X) : z ∈ (R : Subgroup X) :=
  CFSG.pCore_isPGroup.le_sylow_of_normal R (mem_pCore_of_mem_center hz hzp)

end Center

namespace ReducedNongeneration

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem exists_of_ne_component_of_center (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K₁ K₂ : Subgroup X}
    (h₁ : IsComponentOf K₁ ⊤) (h₂ : IsComponentOf K₂ ⊤) (hne : K₁ ≠ K₂) :
    ∃ U ≤ (R : Subgroup X) ⊓ CFSG.generalizedFitting X, 2 ≤ Open.pRank p U ∧
      K₁ ≤ Subgroup.centralizer (U : Set X) ∧
      ∃ t ∈ (R : Subgroup X) ⊓ K₁, orderOf t = p ∧ t ∉ U := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t₂, ⟨ht₂R, ht₂K⟩, ht₂, ht₂Z⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R h₂
  obtain ⟨t₁, ⟨ht₁R, ht₁K⟩, ht₁, ht₁Z⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R h₁
  have hzR := mem_sylow_of_mem_center hz hzp R
  have hzF : z ∈ CFSG.generalizedFitting X :=
    Subgroup.mem_sup_left (CFSG.pCore_le_fitting X p (mem_pCore_of_mem_center hz hzp))
  have hUC : Subgroup.zpowers z ⊔ Subgroup.zpowers t₂ ≤ Subgroup.centralizer (K₁ : Set X) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.center_le_centralizer _ hz))
      (Subgroup.zpowers_le.mpr (le_centralizer_of_component_ne h₂ h₁ hne.symm ht₂K))
  refine ⟨Subgroup.zpowers z ⊔ Subgroup.zpowers t₂,
    sup_le (Subgroup.zpowers_le.mpr ⟨hzR, hzF⟩) (Subgroup.zpowers_le.mpr
      ⟨ht₂R, Subgroup.mem_sup_right (le_layer_of_isComponentOf h₂ ht₂K)⟩),
    two_le_pRank_of_commute_of_not_mem_zpowers hp hzp (ht₂ ▸ pow_orderOf_eq_one t₂)
      (fun ht => ht₂Z (Subgroup.zpowers_le.mpr (Subgroup.center_le_centralizer _ hz) ht))
      (Subgroup.mem_center_iff.mp hz t₂).symm
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₂)),
    Subgroup.le_centralizer_iff.mp hUC, t₁, ⟨ht₁R, ht₁K⟩, ht₁, fun ht => ht₁Z (hUC ht)⟩

theorem le_of_ne_component_of_center (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K₁ K₂ : Subgroup X}
    (h₁ : IsComponentOf K₁ ⊤) (h₂ : IsComponentOf K₂ ⊤) (hne : K₁ ≠ K₂) : K₁ ≤ X₀ := by
  obtain ⟨U, hU, hU2, hKU, t, ⟨htR, htK⟩, ht, htU⟩ :=
    h.exists_of_ne_component_of_center hz hzp h₁ h₂ hne
  exact (hKU.trans (Subgroup.centralizer_le_normalizer _)).trans
    (h.normalizer_le_of_mem_centralizer htR htU ht (hKU htK) (hU.trans inf_le_left) hU2)

theorem eq_of_isComponentOf_of_center (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K₁ K₂ : Subgroup X}
    (h₁ : IsComponentOf K₁ ⊤) (h₂ : IsComponentOf K₂ ⊤) : K₁ = K₂ := by
  by_contra hne
  have hp := h.prime
  have hall : ∀ L : Subgroup X, IsComponentOf L ⊤ → L ≤ X₀ := by
    intro L hL
    by_cases hL₁ : L = K₁
    · rw [hL₁]
      exact h.le_of_ne_component_of_center hz hzp h₁ h₂ hne
    · exact h.le_of_ne_component_of_center hz hzp hL h₁ hL₁
  obtain ⟨U, hU, hU2, hKU, t, ⟨htR, htK⟩, ht, htU⟩ :=
    h.exists_of_ne_component_of_center hz hzp h₁ h₂ hne
  obtain ⟨E, hEU, hE, hEcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp hU2
  refine not_layer_le_of_weakCore_le hp h.core_eq_bot R h.weakCore_le h.ne_top ?_
    (sSup_le fun L hL => hall L ((CFSG.isComponent_iff_open L).mp hL))
  exact three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hE hEcard ht
    (fun htE => htU (hEU htE)) (Subgroup.centralizer_le hEU (hKU htK)) (hEU.trans hU)
    ⟨htR, Subgroup.mem_sup_right (le_layer_of_isComponentOf h₁ htK)⟩

theorem normal_of_isComponentOf_of_center (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) : K.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have heq := h.eq_of_isComponentOf_of_center hz hzp
    ((ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).mpr hK) hK
  rw [← heq]
  exact ⟨n, hn, rfl⟩

theorem mem_or_rankOne_of_center (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) :
    (z ∈ (Subgroup.center K).map K.subtype ∧
        ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X)) ∨
      (z ∉ K ∧ Subgroup.center K = ⊥ ∧ (¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X) →
        (∀ U : Subgroup X, U ≤ (R : Subgroup X) ⊓ K → U ≠ ⊥ →
          K ⊓ Subgroup.normalizer (U : Set X) ≤ X₀) ∧ ¬ K ≤ X₀)) := by
  have hp := h.prime
  have hzR := mem_sylow_of_mem_center hz hzp R
  have hzc : z ∈ Subgroup.centralizer (K : Set X) := Subgroup.center_le_centralizer _ hz
  by_cases hzK : z ∈ K
  · have hzZ : (⟨z, hzK⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun k => Subtype.ext (Subgroup.mem_center_iff.mp hz k)
    refine Or.inl ⟨⟨_, hzZ, rfl⟩, fun hcyc => ?_⟩
    rw [h.center_eq_bot_of_isCyclic hK hcyc, Subgroup.mem_bot] at hzZ
    have hz1 : z = 1 := congrArg Subtype.val hzZ
    rw [hz1, orderOf_one] at hzp
    exact hp.one_lt.ne hzp
  · refine Or.inr ⟨hzK, ?_, fun hnc => h.rankOne_principle hK hnc hzR hzK hzp hzc⟩
    by_cases hcyc : IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X)
    · exact h.center_eq_bot_of_isCyclic hK hcyc
    · exact h.center_eq_bot_of_rankOne hK hcyc hzR hzK hzp hzc

end ReducedNongeneration

section Centralizer

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem mk_mem_center_centralizer {z : G} (O : Subgroup (Subgroup.centralizer ({z} : Set G)))
    [O.Normal] {zC : Subgroup.centralizer ({z} : Set G)} (hzC : (zC : G) = z) :
    QuotientGroup.mk' O zC ∈ Subgroup.center (Subgroup.centralizer ({z} : Set G) ⧸ O) := by
  have hzZ : zC ∈ Subgroup.center (Subgroup.centralizer ({z} : Set G)) := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hzC]
    exact Subgroup.mem_centralizer_singleton_iff.mp c.2
  exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective O) ⟨zC, hzZ, rfl⟩

theorem orderOf_mk_of_coprime {Y : Type*} [Group Y] [Finite Y] (hp : p.Prime) (O : Subgroup Y)
    [O.Normal] (hO : p.Coprime (Nat.card O)) {y : Y} (hyp : orderOf y = p) :
    orderOf (QuotientGroup.mk' O y) = p := by
  have : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime (by rw [← map_pow, ← hyp, pow_orderOf_eq_one, map_one]) fun h1 => ?_
  have hyO : y ∈ Subgroup.zpowers y ⊓ O :=
    ⟨Subgroup.mem_zpowers y, by rwa [← QuotientGroup.ker_mk' O]⟩
  rw [inf_eq_bot_of_isPGroup hp
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyp, pow_one])) hO,
    Subgroup.mem_bot] at hyO
  rw [hyO, orderOf_one] at hyp
  exact hp.one_lt.ne hyp

theorem reducedNongeneration_centralizer_of_not_le (hp : p.Prime) (hp2 : p ≠ 2) (P : Sylow p G)
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M) (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    (hP : 3 ≤ Open.pRank p (P : Subgroup G)) {z : G}
    (hzc : z ∈ Subgroup.centralizer ((P : Subgroup G) : Set G)) (hzp : orderOf z = p)
    (hCM : ¬ Subgroup.centralizer ({z} : Set G) ≤ M)
    (hcore : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M) :
    ∃ Pbar : Sylow p (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p),
      (Pbar : Subgroup _) = ((P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore p)) ∧
      ReducedNongeneration p (Subgroup.centralizer ({z} : Set G) ⧸
          primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) Pbar
        (((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
          (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' (primeComplementCore p))) ∧
      ∀ zC : Subgroup.centralizer ({z} : Set G), (zC : G) = z →
        QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) zC ∈
          Subgroup.center (Subgroup.centralizer ({z} : Set G) ⧸
            primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) ∧
        orderOf (QuotientGroup.mk'
          (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) zC) = p := by
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc x hx)
  have hPmap : ((P.subtype hPC : Sylow p _) : Subgroup _).map
      (Subgroup.centralizer ({z} : Set G)).subtype = P := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPC]
  obtain ⟨Pbar, hPbar, hred⟩ := reducedNongeneration_of_not_le hp hp2 P hPM hWM hCM
    (P.subtype hPC) hPmap.le (hPmap ▸ hP) hcore
  refine ⟨Pbar, by rw [hPbar, Sylow.coe_subtype], hred, fun zC hzC =>
    ⟨mk_mem_center_centralizer _ hzC, orderOf_mk_of_coprime hp _ (primeComplementCore_coprime p)
      (by rw [← Subgroup.orderOf_coe, hzC, hzp])⟩⟩

end Centralizer

theorem D1Extremal.exists_reducedNongeneration_of_hasPrimeConstraint {G : Type} [Group G]
    [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hloc : D1Local p P M)
    {H R : Subgroup G} (h : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p) :
    ∃ z : G, z ∈ R ∧ orderOf z = p ∧ z ∈ Subgroup.centralizer (P : Set G) ∧
      (∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ (P : Subgroup G) → orderOf y = p →
        y ∈ Subgroup.zpowers z) ∧
      ¬ Subgroup.centralizer ({z} : Set G) ≤ M ∧
      GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M ∧
      Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) ∧
      ∃ Pbar : Sylow p (Subgroup.centralizer ({z} : Set G) ⧸
          primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p),
        (Pbar : Subgroup _) = ((P : Subgroup G).subgroupOf
          (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' (primeComplementCore p)) ∧
        ReducedNongeneration p (Subgroup.centralizer ({z} : Set G) ⧸
            primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) Pbar
          (((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
            (Subgroup.centralizer ({z} : Set G))).map
              (QuotientGroup.mk' (primeComplementCore p))) ∧
        (∀ zC : Subgroup.centralizer ({z} : Set G), (zC : G) = z →
          QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) zC ∈
            Subgroup.center (Subgroup.centralizer ({z} : Set G) ⧸
              primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) ∧
          orderOf (QuotientGroup.mk'
            (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) zC) = p) ∧
        ∃ K : Subgroup (Subgroup.centralizer ({z} : Set G) ⧸
            primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p),
          IsComponentOf K ⊤ ∧ K.Normal ∧ ∀ L, IsComponentOf L ⊤ → L = K := by
  have hp := h.prime
  obtain ⟨z, hzR, hzp, hzc, huniq, hCM, hcoreM, hodd, hlayer⟩ :=
    h.exists_central_of_hasPrimeConstraint hloc hcon
  obtain ⟨Pbar, hPbar, hred, hzbar⟩ := reducedNongeneration_centralizer_of_not_le hp h.ne_two P
    h.sylow_le h.weakCore_le
    (h.three_le_pRank.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp h.le_P))
    hzc hzp hCM hcoreM
  obtain ⟨hzZ, hzbarp⟩ := hzbar ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ rfl
  obtain ⟨K, hK⟩ := exists_isComponentOf_of_layer_ne_bot hlayer
  exact ⟨z, hzR, hzp, hzc, huniq, hCM, hcoreM, hodd, Pbar, hPbar, hred, hzbar, K, hK,
    hred.normal_of_isComponentOf_of_center hzZ hzbarp hK,
    fun L hL => hred.eq_of_isComponentOf_of_center hzZ hzbarp hL hK⟩

theorem D1Extremal.exists_unique_component_of_hasPrimeConstraint {G : Type} [Group G] [Finite G]
    {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hloc : D1Local p P M)
    {H R : Subgroup G} (h : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p) :
    ∃ z : G, z ∈ R ∧ orderOf z = p ∧ z ∈ Subgroup.centralizer (P : Set G) ∧
      ¬ Subgroup.centralizer ({z} : Set G) ≤ M ∧
      ∃ K : Subgroup (Subgroup.centralizer ({z} : Set G) ⧸
          primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p),
        IsComponentOf K ⊤ ∧ K.Normal ∧
        ∀ L, IsComponentOf L ⊤ → L = K := by
  obtain ⟨z, hzR, hzp, hzc, -, hCM, -, -, -, -, -, -, hK⟩ :=
    h.exists_reducedNongeneration_of_hasPrimeConstraint hloc hcon
  exact ⟨z, hzR, hzp, hzc, hCM, hK⟩

end CFSG.AGLEmbedding
