module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRSetup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRTransfer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRTwoBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.TRoute

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_subgroupOf_le_gnC {M X₀ T : Subgroup G} (hXM : X₀ ≤ M) (hTX : T ≤ X₀)
    (hQT : pCoreOf 2 M ≤ T) :
    (pCoreOf 2 M).subgroupOf X₀ ≤ gnC (T.subgroupOf X₀) := by
  have hQX : pCoreOf 2 M ≤ X₀ := hQT.trans hTX
  set Qh : Subgroup ↥X₀ := (pCoreOf 2 M).subgroupOf X₀ with hQh
  have hQhn : Qh.Normal := by
    rw [hQh, Subgroup.normal_subgroupOf_iff_le_normalizer hQX]
    exact hXM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have : (Subgroup.centralizer (Qh : Set ↥X₀)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro q hq
    have hq' : g⁻¹ * q * g ∈ Qh := by
      have := hQhn.conj_mem q hq g⁻¹
      simpa using this
    have := hn _ hq'
    calc q * (g * n * g⁻¹) = g * ((g⁻¹ * q * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * q * g)) * g⁻¹ := by rw [this]
      _ = g * n * g⁻¹ * q := by group⟩
  have hV : gnV (T.subgroupOf X₀) ≤ Subgroup.centralizer (Qh : Set ↥X₀) := by
    refine Subgroup.normalClosure_le_normal fun z hz q hq => ?_
    have hzc : z ∈ Quasithin.centerOf (T.subgroupOf X₀) :=
      ((Subgroup.closure_le _).mpr fun _ hx => hx.1 :
        Quasithin.omegaOneCenterOf (T.subgroupOf X₀) ≤ Quasithin.centerOf (T.subgroupOf X₀)) hz
    have hqT : q ∈ T.subgroupOf X₀ := Subgroup.mem_subgroupOf.mpr (hQT (Subgroup.mem_subgroupOf.mp hq))
    exact (Subgroup.mem_centralizer_iff.mp hzc.2 q hqT)
  intro q hq
  rw [gnC, Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (hV hv) q hq).symm

theorem mem_trJ_of_pow_three {M L₁ L₂ T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hN : ∀ t ∈ T, ∀ j ∈ trJ M L₁ L₂, t * j * t⁻¹ ∈ trJ M L₁ L₂) {x : G}
    (hx : x ∈ trX M L₁ L₂ T) (h3 : x ^ 3 = 1) : x ∈ trJ M L₁ L₂ := by
  have hle : trX M L₁ L₂ T ≤ Subgroup.normalizer (trJ M L₁ L₂ : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro j
    refine ⟨fun hj => hN t ht j hj, fun hj => ?_⟩
    have := hN t⁻¹ (T.inv_mem ht) _ hj
    simpa [mul_assoc] using this
  set J := trJ M L₁ L₂ with hJ
  have : (J.subgroupOf (trX M L₁ L₂ T)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_trX_left]
    exact hle
  obtain ⟨t, ht, j, hj, rfl⟩ := exists_mul_of_mem_trX hN hx
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  let t' : ↥(trX M L₁ L₂ T) := ⟨t, le_trX_right ht⟩
  let j' : ↥(trX M L₁ L₂ T) := ⟨j, le_trX_left hj⟩
  have hj'D : j' ∈ J.subgroupOf (trX M L₁ L₂ T) := Subgroup.mem_subgroupOf.mpr hj
  have hq : (QuotientGroup.mk (t' * j') : ↥(trX M L₁ L₂ T) ⧸ J.subgroupOf (trX M L₁ L₂ T)) =
      QuotientGroup.mk t' := by
    rw [QuotientGroup.eq]
    simpa using (J.subgroupOf (trX M L₁ L₂ T)).inv_mem hj'D
  have h3' : (QuotientGroup.mk (t' * j') :
      ↥(trX M L₁ L₂ T) ⧸ J.subgroupOf (trX M L₁ L₂ T)) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (t' * j') ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [this]; rfl
  rw [hq] at h3'
  have h2 : (QuotientGroup.mk t' : ↥(trX M L₁ L₂ T) ⧸ J.subgroupOf (trX M L₁ L₂ T)) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : t' ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [this]; rfl
  have hd1 : orderOf (QuotientGroup.mk t' : ↥(trX M L₁ L₂ T) ⧸ J.subgroupOf (trX M L₁ L₂ T)) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one h3'
  have hd2 : orderOf (QuotientGroup.mk t' : ↥(trX M L₁ L₂ T) ⧸ J.subgroupOf (trX M L₁ L₂ T)) ∣
      2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime 3 (2 ^ k) :=
    Nat.Coprime.pow_right k (by norm_num)
  have hord := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  have h1 : (QuotientGroup.mk t' : ↥(trX M L₁ L₂ T) ⧸ J.subgroupOf (trX M L₁ L₂ T)) = 1 :=
    orderOf_eq_one_iff.mp hord
  have ht'D : t' ∈ J.subgroupOf (trX M L₁ L₂ T) := (QuotientGroup.eq_one_iff t').mp h1
  exact J.mul_mem (Subgroup.mem_subgroupOf.mp ht'D) hj

omit [Finite G] in
theorem barM_sup_eq {M A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) :
    barM M (A ⊔ B) = barM M A ⊔ barM M B := by
  rw [barM, barM, barM, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

omit [Finite G] in
theorem barM_pCoreOf_eq_bot (M : Subgroup G) : barM M (pCoreOf 2 M) = ⊥ := by
  rw [barM, Subgroup.map_eq_bot_iff]
  intro q hq
  exact (mk_eq_one_iff_coe_mem_pCoreOf q).mpr (Subgroup.mem_subgroupOf.mp hq)

omit [Finite G] in
theorem mem_barM_iff' {M X : Subgroup G} {x : ↥M ⧸ CFSG.pCore 2 ↥M} :
    x ∈ barM M X ↔ ∃ m : ↥M, (m : G) ∈ X ∧ QuotientGroup.mk' (CFSG.pCore 2 ↥M) m = x := by
  simp only [barM, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem not_three_dvd_gnC {M H L₁ L₂ T : Subgroup G}
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (hT2 : IsPGroup 2 T) (hTH : T ≤ H) (hTM : T ≤ M) (hQT : pCoreOf 2 M ≤ T)
    (hZ₁ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₁)))
    (hZ₂ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₂)))
    (hmove₁ : ¬ L₁.subgroupOf (trX M L₁ L₂ T) ≤ gnC (T.subgroupOf (trX M L₁ L₂ T)))
    (hmove₂ : ¬ L₂.subgroupOf (trX M L₁ L₂ T) ≤ gnC (T.subgroupOf (trX M L₁ L₂ T))) :
    ¬ 3 ∣ Nat.card (gnC (T.subgroupOf (trX M L₁ L₂ T))) := by
  intro hdvd
  have hN := normalizes_trJ h₁ h₂ hk2 hTM
    (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hXM : trX M L₁ L₂ T ≤ M := trX_le h₁.le h₂.le hTM
  set X₀ := trX M L₁ L₂ T with hX₀
  set J := trJ M L₁ L₂ with hJ
  set C := gnC (T.subgroupOf X₀) with hC
  have hker : (pCoreOf 2 M).subgroupOf X₀ ≤ C :=
    pCoreOf_subgroupOf_le_gnC hXM le_trX_right hQT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨c, hcC⟩, hc3⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hc3' : c ^ 3 = 1 := by
    have := pow_orderOf_eq_one (⟨c, hcC⟩ : ↥C)
    rw [hc3] at this
    simpa using congrArg Subtype.val this
  have hcJ : ((c : ↥X₀) : G) ∈ J := mem_trJ_of_pow_three hT2 hN c.2 (by
    simpa using congrArg (fun y : ↥X₀ => (y : G)) hc3')
  set Cg : Subgroup G := C.map X₀.subtype with hCg
  set N : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := barM M (Cg ⊓ J) with hNdef
  have hJM : J ≤ M := sup_le (sup_le h₁.le h₂.le) (pCoreOf_le 2 M)
  have hJX : J ≤ X₀ := le_trX_left
  have hbJ : barM M J = barM M L₁ ⊔ barM M L₂ := by
    rw [hJ, trJ, barM_sup_eq (sup_le h₁.le h₂.le) (pCoreOf_le 2 M), barM_sup_eq h₁.le h₂.le,
      barM_pCoreOf_eq_bot, sup_bot_eq]
  have hNle : N ≤ barM M L₁ ⊔ barM M L₂ := hbJ ▸ barM_mono inf_le_right
  have hNn : ∀ x ∈ barM M L₁ ⊔ barM M L₂, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    intro x hx n hn
    rw [← hbJ] at hx
    obtain ⟨m, hmJ, rfl⟩ := mem_barM_iff'.mp hx
    obtain ⟨mc, ⟨hmcC, hmcJ⟩, rfl⟩ := mem_barM_iff'.mp hn
    refine mem_barM_iff'.mpr ⟨m * mc * m⁻¹, ⟨?_, ?_⟩, by simp⟩
    · obtain ⟨cc, hcc, hccv⟩ := hmcC
      have hccv' : ((cc : ↥X₀) : G) = (mc : G) := hccv
      let mX : ↥X₀ := ⟨m, hJX hmJ⟩
      refine ⟨mX * cc * mX⁻¹, (inferInstance : C.Normal).conj_mem cc hcc mX, ?_⟩
      show ((mX * cc * mX⁻¹ : ↥X₀) : G) = (m : G) * (mc : G) * (m : G)⁻¹
      simp [mX, hccv']
    · exact J.mul_mem (J.mul_mem hmJ hmcJ) (J.inv_mem hmJ)
  have hnot : ∀ L : Subgroup G, L ≤ M → ¬ L.subgroupOf X₀ ≤ C → ¬ barM M L ≤ N := by
    intro L hLM hmove hle
    apply hmove
    intro l hl
    have hlM : (l : G) ∈ M := hXM l.2
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlM⟩ ∈ barM M L :=
      mem_barM_iff'.mpr ⟨⟨l, hlM⟩, Subgroup.mem_subgroupOf.mp hl, rfl⟩
    obtain ⟨y, ⟨hyC, hyJ⟩, hy⟩ := mem_barM_iff'.mp (hle hmem)
    obtain ⟨cc, hcc, hccv⟩ := hyC
    have hccv' : ((cc : ↥X₀) : G) = (y : G) := hccv
    have hq : (y : ↥M)⁻¹ * ⟨l, hlM⟩ ∈ CFSG.pCore 2 ↥M := by
      rw [← QuotientGroup.eq]
      exact hy
    have hz : (y : G)⁻¹ * (l : G) ∈ pCoreOf 2 M := by
      have h2 : (y : G)⁻¹ * (l : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype :=
        ⟨(y : ↥M)⁻¹ * ⟨l, hlM⟩, hq, rfl⟩
      assumption
    have hz' : cc⁻¹ * l ∈ (pCoreOf 2 M).subgroupOf X₀ := by
      rw [Subgroup.mem_subgroupOf]
      show ((cc : ↥X₀) : G)⁻¹ * (l : G) ∈ pCoreOf 2 M
      rw [hccv']
      exact hz
    have := C.mul_mem hcc (hker hz')
    simpa using this
  have hcomm : ∀ a ∈ barM M L₁, ∀ b ∈ barM M L₂, a * b = b * a := by
    have hc : ⁅barM M L₁, barM M L₂⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ h₁.component h₂.component hne
    intro a ha b hb
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    exact (Subgroup.mem_centralizer_iff.mp (this ha) b hb).symm
  have hcN : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(c : G), hXM c.2⟩ ∈ N :=
    mem_barM_iff'.mpr ⟨⟨(c : G), hXM c.2⟩, ⟨⟨c, hcC, rfl⟩, hcJ⟩, rfl⟩
  have h1 := eq_one_of_three_pow_of_normal_sup h₁.component h₂.component hcomm hZ₁ hZ₂ hNle hNn
    (hnot L₁ h₁.le hmove₁) (hnot L₂ h₂.le hmove₂) hcN ⟨1, by
      rw [pow_one, ← map_pow]
      have : ((⟨(c : G), hXM c.2⟩ : ↥M)) ^ 3 = 1 := Subtype.ext (by simpa using congrArg (fun y : ↥X₀ => (y : G)) hc3')
      rw [this, map_one]⟩
  have hcQ : (c : G) ∈ pCoreOf 2 M := (mk_eq_one_iff_coe_mem_pCoreOf ⟨(c : G), hXM c.2⟩).mp h1
  obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 M ⟨(c : G), hcQ⟩
  have ha' : (c : G) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hd1 : orderOf (c : G) ∣ 3 := orderOf_dvd_of_pow_eq_one (by simpa using congrArg (fun y : ↥X₀ => (y : G)) hc3')
  have hd2 : orderOf (c : G) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one ha'
  have := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 3 2)) hd1 hd2
  have hc1 : (c : G) = 1 := orderOf_eq_one_iff.mp this
  have hc1' : c = 1 := Subtype.ext hc1
  have hC1 : (⟨c, hcC⟩ : ↥C) = 1 := Subtype.ext hc1'
  rw [hC1, orderOf_one] at hc3
  exact absurd hc3 (by norm_num)

omit [Finite G] in
theorem characteristic_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {K : Subgroup A} [hK : K.Characteristic] : (K.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  have hψ := (Subgroup.characteristic_iff_map_eq.mp hK) (e.trans (φ.trans e.symm))
  rw [Subgroup.map_map]
  have : φ.toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp (e.trans (φ.trans e.symm)).toMonoidHom := by
    ext x; simp
  rw [this, ← Subgroup.map_map, hψ]

theorem gnBound_of_pair {P : Sylow 3 G} {M A H R : Subgroup G}
    (hctx : PairStrongCtx P M A H R) (hK : KFactStrongThreeSolv) {X₀ T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTX : T ≤ X₀) (hXM : X₀ ≤ M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) : GNBound (T.subgroupOf X₀) := by
  intro T' hT'b hT'T hchar
  set T'' : Subgroup G := T'.map X₀.subtype with hT''
  have hT''T : T'' ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hT'T hx)
  have hT''b : T'' ≠ ⊥ := by
    intro h
    apply hT'b
    have hle := (Subgroup.map_eq_bot_iff _).mp h
    have hk : X₀.subtype.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr X₀.subtype_injective
    rw [hk] at hle
    exact le_bot_iff.mp hle
  have hchar'' : (T''.subgroupOf T).Characteristic := by
    let e := Subgroup.subgroupOfEquivOfLe hTX
    have h1 : ((T'.subgroupOf (T.subgroupOf X₀)).map e.toMonoidHom).Characteristic := by
      have := hchar
      exact characteristic_map_mulEquiv e
    have h2 : (T'.subgroupOf (T.subgroupOf X₀)).map e.toMonoidHom = T''.subgroupOf T := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine Subgroup.mem_subgroupOf.mpr ⟨(x : ↥X₀), Subgroup.mem_subgroupOf.mp hx, rfl⟩
      · intro hy
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_subgroupOf.mp hy
        refine ⟨⟨x, Subgroup.mem_subgroupOf.mpr (by
          have : (x : G) = (y : G) := hxy
          rw [this]; exact y.2)⟩, Subgroup.mem_subgroupOf.mpr hx, Subtype.ext hxy⟩
    rwa [h2] at h1
  have hNC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (T'' : Set G) := by
    have := @CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic G _ T
      (T''.subgroupOf T) hchar''
    rwa [Subgroup.map_subgroupOf_eq_of_le hT''T] at this
  obtain ⟨hr, hp⟩ := hctx.normalizer_char_facts hK hT2 hNT hT''b hT''T hNC
  have hmap : (Subgroup.normalizer (T' : Set ↥X₀)).map X₀.subtype ≤
      Subgroup.normalizer (T'' : Set G) ⊓ M := by
    rintro _ ⟨x, hx, rfl⟩
    have hx : x ∈ Subgroup.normalizer (T' : Set ↥X₀) := hx
    refine ⟨?_, hXM x.2⟩
    show X₀.subtype x ∈ Subgroup.normalizer (T'' : Set G)
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨x * y' * x⁻¹, (hx y').mp hy', by simp⟩
    · rintro hy'
      obtain ⟨z, hz, hzy⟩ := hy'
      have hzy' : (z : G) = (x : G) * y * (x : G)⁻¹ := hzy
      have hz' : (x⁻¹ * z * x : ↥X₀) ∈ T' := by
        refine (hx (x⁻¹ * z * x)).mpr ?_
        have e1 : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
        rw [e1]
        exact hz
      refine ⟨x⁻¹ * z * x, hz', ?_⟩
      show (((x⁻¹ * z * x : ↥X₀)) : G) = y
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzy']
      group
  have hrk : Open.pRank 3 (Subgroup.normalizer (T' : Set ↥X₀)) ≤ Open.pRank 3 (Subgroup.normalizer (T'' : Set G) ⊓ M) := by
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three X₀.subtype X₀.subtype_injective]
    exact CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hmap
  refine ⟨hrk.trans hr, fun h2 J hJ hJp => ?_⟩
  have hD := hp (h2.trans hrk)
  have hJmap : J.map X₀.subtype ≤ Subgroup.normalizer (T'' : Set G) ⊓ M :=
    (Subgroup.map_mono hJ).trans hmap
  have hJp' : ⁅J.map X₀.subtype, J.map X₀.subtype⁆ = J.map X₀.subtype := by
    rw [← Subgroup.map_commutator, hJp]
  have := hD _ hJmap hJp'
  rwa [Subgroup.card_map_of_injective X₀.subtype_injective] at this

end CFSG.AGLEmbeddingD2.McLaughlin
