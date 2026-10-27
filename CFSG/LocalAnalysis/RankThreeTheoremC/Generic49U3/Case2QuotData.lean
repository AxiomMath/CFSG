module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Case2AbDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Config
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (PGroupDataAb Case2DataAb)

section Generic

variable {p : ℕ}

private theorem card_map_of_injOn' {H Y : Type*} [Group H] [Group Y] (φ : H →* Y) {T : Subgroup H}
    (hinj : Set.InjOn φ (T : Set H)) : Nat.card (T.map φ) = Nat.card T := by
  have h := Nat.card_image_of_injOn hinj
  rw [← Subgroup.coe_map] at h
  exact h

private theorem PGroupData.map_of_injOn {H Y : Type*} [Group H] [Group Y] (hp : p.Prime) (φ : H →* Y)
    {P T D : Subgroup H} {x : H} (hinj : Set.InjOn φ (P : Set H)) (h : PGroupData p P T D x) :
    PGroupData p (P.map φ) (T.map φ) (D.map φ) (φ x) where
  T_le := Subgroup.map_mono h.T_le
  D_le := Subgroup.map_mono h.D_le
  sup_eq := by rw [← Subgroup.map_sup, h.sup_eq]
  inf_eq := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨t, ht, rfl⟩, ⟨d, hd, hdt⟩⟩
    have htd : d = t := hinj (h.D_le hd) (h.T_le ht) hdt
    have : t ∈ T ⊓ D := ⟨ht, htd ▸ hd⟩
    rw [h.inf_eq, Subgroup.mem_bot] at this
    simp [this]
  comm := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul, h.comm t ht d hd]
  T_card := by
    rw [card_map_of_injOn' φ (hinj.mono (SetLike.coe_subset_coe.mpr h.T_le))]
    exact h.T_card
  T_exp := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, h.T_exp t ht, map_one]
  T_nonab := by
    intro hc
    apply h.T_nonab
    rw [isMulCommutative_iff_of_setLike]
    intro a ha b hb
    have hab : φ a * φ b = φ b * φ a :=
      isMulCommutative_iff_of_setLike.mp hc (φ a) ⟨a, ha, rfl⟩ (φ b) ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul] at hab
    exact hinj (P.mul_mem (h.T_le ha) (h.T_le hb)) (P.mul_mem (h.T_le hb) (h.T_le ha)) hab
  D_cyc := by
    haveI := h.D_cyc
    exact isCyclic_of_surjective (φ.subgroupMap D) (φ.subgroupMap_surjective D)
  x_mem := Subgroup.mem_map_of_mem φ h.x_mem
  x_ord := by
    have hxP : x ∈ P := h.D_le h.x_mem
    have hdvd : orderOf (φ x) ∣ p := h.x_ord ▸ orderOf_map_dvd φ x
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exfalso
      have h1' : φ x = 1 := orderOf_eq_one_iff.mp h1
      have : x = 1 := hinj hxP P.one_mem (by rw [h1', map_one])
      have h2 : orderOf x = 1 := orderOf_eq_one_iff.mpr this
      rw [h.x_ord] at h2
      exact hp.ne_one h2
    · exact h1


private theorem PGroupData.subgroupOf {G : Type*} [Group G] {P T D : Subgroup G} {x : G}
    (M : Subgroup G) (hPM : P ≤ M) (hxM : x ∈ M) (h : PGroupData p P T D x) :
    PGroupData p (P.subgroupOf M) (T.subgroupOf M) (D.subgroupOf M) (⟨x, hxM⟩ : M) where
  T_le := fun a ha => h.T_le ha
  D_le := fun a ha => h.D_le ha
  sup_eq := by
    rw [← Subgroup.subgroupOf_sup (h.T_le.trans hPM) (h.D_le.trans hPM), h.sup_eq]
  inf_eq := by
    rw [eq_bot_iff]
    intro a ha
    have : (a : G) ∈ T ⊓ D := ⟨ha.1, ha.2⟩
    rw [h.inf_eq, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  comm := fun t ht d hd => Subtype.ext (h.comm t ht d hd)
  T_card := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.T_le.trans hPM)).toEquiv]
    exact h.T_card
  T_exp := fun t ht => Subtype.ext (by simpa using h.T_exp t ht)
  T_nonab := by
    intro hc
    apply h.T_nonab
    rw [isMulCommutative_iff_of_setLike]
    intro a ha b hb
    have := isMulCommutative_iff_of_setLike.mp hc ⟨a, (h.T_le.trans hPM) ha⟩ ha
      ⟨b, (h.T_le.trans hPM) hb⟩ hb
    exact congrArg Subtype.val this
  D_cyc := by
    have := h.D_cyc
    exact (Subgroup.subgroupOfEquivOfLe (h.D_le.trans hPM)).symm.isCyclic.mp h.D_cyc
  x_mem := h.x_mem
  x_ord := by
    rw [Subgroup.orderOf_mk]
    exact h.x_ord

private theorem zOf_map_of_injOn {H Y : Type*} [Group H] [Group Y] (φ : H →* Y) {T : Subgroup H}
    (hinj : Set.InjOn φ (T : Set H)) : zOf (T.map φ) = (zOf T).map φ := by
  ext y
  constructor
  · rintro ⟨⟨t₀, ht₀, rfl⟩, hy⟩
    refine ⟨t₀, ⟨ht₀, Subgroup.mem_centralizer_iff.mpr ?_⟩, rfl⟩
    intro t ht
    have := Subgroup.mem_centralizer_iff.mp hy (φ t) (Subgroup.mem_map_of_mem φ ht)
    rw [← map_mul, ← map_mul] at this
    exact hinj (T.mul_mem ht ht₀) (T.mul_mem ht₀ ht) this
  · rintro ⟨z, ⟨hzT, hzc⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem φ hzT, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hzc t ht]

private theorem zOf_subgroupOf {G : Type*} [Group G] {T : Subgroup G} (M : Subgroup G) (hTM : T ≤ M) :
    zOf (T.subgroupOf M) = (zOf T).subgroupOf M := by
  ext a
  simp only [zOf, Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨haT, hac⟩
    refine ⟨haT, fun t ht => ?_⟩
    exact congrArg Subtype.val (hac ⟨t, hTM ht⟩ ht)
  · rintro ⟨haT, hac⟩
    refine ⟨haT, fun t ht => ?_⟩
    exact Subtype.ext (hac t ht)


private theorem TorusProps.map_of_injOn {H Y : Type*} [Group H] [Group Y] (φ : H →* Y) {T F : Subgroup H}
    (hinj : Set.InjOn φ (T : Set H)) (h : TorusProps p T F) :
    TorusProps p (T.map φ) (F.map φ) where
  F_T := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨t, ht, rfl⟩
    exact ⟨f * t * f⁻¹, h.F_T f hf t ht, by simp⟩
  irred := by
    intro A hAT hzA hFA
    rw [zOf_map_of_injOn φ hinj] at hzA ⊢
    have hA : (A.comap φ ⊓ T).map φ = A := CFSG.AGLEmbedding.map_comap_inf_eq φ hAT
    have h1 := h.irred (A.comap φ ⊓ T) inf_le_right ?_ ?_
    · rcases h1 with h1 | h1
      · left; rw [← hA, h1]
      · right; rw [← hA, h1]
    · intro z hz
      exact ⟨hzA (Subgroup.mem_map_of_mem φ hz), hz.1⟩
    · intro f hf a ha
      refine ⟨?_, h.F_T f hf a ha.2⟩
      show φ (f * a * f⁻¹) ∈ A
      rw [map_mul, map_mul, map_inv]
      exact hFA (φ f) (Subgroup.mem_map_of_mem φ hf) (φ a) ha.1
  fpf := by
    rintro _ ⟨t₀, ht₀, rfl⟩ hf
    rw [zOf_map_of_injOn φ hinj] at hf ⊢
    refine Subgroup.mem_map_of_mem φ (h.fpf t₀ ht₀ fun f hf' => ?_)
    obtain ⟨z, hz, hzeq⟩ := hf (φ f) (Subgroup.mem_map_of_mem φ hf')
    have hmem : f * t₀ * f⁻¹ * t₀⁻¹ ∈ T :=
      T.mul_mem (h.F_T f hf' t₀ ht₀) (T.inv_mem ht₀)
    have : f * t₀ * f⁻¹ * t₀⁻¹ = z :=
      hinj hmem hz.1 (by rw [hzeq]; simp)
    rw [this]
    exact hz
  onto := by
    intro z hz k hk
    rw [zOf_map_of_injOn φ hinj] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    obtain ⟨f, hf, hfz⟩ := h.onto z₀ hz₀ k hk
    refine ⟨φ f, Subgroup.mem_map_of_mem φ hf, ?_⟩
    have := congrArg φ hfz
    simpa [map_mul, map_inv, map_pow] using this

private theorem TorusProps.subgroupOf {G : Type*} [Group G] {T F : Subgroup G} (M : Subgroup G)
    (hTM : T ≤ M) (hFM : F ≤ M) (h : TorusProps p T F) :
    TorusProps p (T.subgroupOf M) (F.subgroupOf M) where
  F_T := fun f hf t ht => h.F_T f hf t ht
  irred := by
    intro A hAT hzA hFA
    rw [zOf_subgroupOf M hTM] at hzA ⊢
    have hmapT : (T.subgroupOf M).map M.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTM
    have hmapZ : ((zOf T).subgroupOf M).map M.subtype = zOf T :=
      Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hTM)
    have h1 := h.irred (A.map M.subtype) ?_ ?_ ?_
    · rcases h1 with h1 | h1
      · left; apply Subgroup.map_injective M.subtype_injective; rw [h1, hmapZ]
      · right; apply Subgroup.map_injective M.subtype_injective; rw [h1, hmapT]
    · rw [← hmapT]; exact Subgroup.map_mono hAT
    · rw [← hmapZ]; exact Subgroup.map_mono hzA
    · rintro f hf _ ⟨a, ha, rfl⟩
      exact ⟨⟨f, hFM hf⟩ * a * ⟨f, hFM hf⟩⁻¹, hFA ⟨f, hFM hf⟩ hf a ha, rfl⟩
  fpf := by
    intro t ht hf
    rw [zOf_subgroupOf M hTM] at hf ⊢
    exact h.fpf t ht fun f hf' => hf ⟨f, hFM hf'⟩ hf'
  onto := by
    intro z hz k hk
    rw [zOf_subgroupOf M hTM] at hz
    obtain ⟨f, hf, hfz⟩ := h.onto z hz k hk
    exact ⟨⟨f, hFM hf⟩, hf, Subtype.ext hfz⟩


private theorem injOn_mk_of_isPGroup {H : Type*} [Group H] [Finite H] (hp : p.Prime) (O : Subgroup H)
    [O.Normal] (hO : p.Coprime (Nat.card O)) {A : Subgroup H} (hA : IsPGroup p A) :
    Set.InjOn (QuotientGroup.mk' O) (A : Set H) := by
  intro a ha b hb hab
  have h1 : a⁻¹ * b ∈ O := QuotientGroup.eq.mp hab
  have h2 : a⁻¹ * b ∈ A ⊓ O := ⟨A.mul_mem (A.inv_mem ha) hb, h1⟩
  rw [CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup hp hA hO, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact h2

private theorem map_conj_zpowers_eq_of_mem {H : Type*} [Group H] [Finite H] (a g : H)
    (h : g * a * g⁻¹ ∈ Subgroup.zpowers a) :
    (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers a := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa using h
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]

private theorem weaklyClosed_map_mk_of_sylow {H : Type*} [Group H] [Finite H] [Fact p.Prime]
    (O : Subgroup H) [O.Normal] {P : Subgroup H} (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) {a : H}
    (ha : IsPGroup p (Subgroup.zpowers a))
    (hwc : ∀ g : H, (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom ≤ P →
      (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers a)
    (g : H ⧸ O)
    (hg : (Subgroup.zpowers (QuotientGroup.mk' O a)).map (MulAut.conj g).toMonoidHom ≤
      P.map (QuotientGroup.mk' O)) :
    (Subgroup.zpowers (QuotientGroup.mk' O a)).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (QuotientGroup.mk' O a) := by
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective O g
  set π := QuotientGroup.mk' O with hπ
  set K : Subgroup H := (P.map π).comap π with hK
  have hPK : P ≤ K := Subgroup.le_comap_map π P
  set Q : Subgroup H := (Subgroup.zpowers a).map (MulAut.conj g₁).toMonoidHom with hQ
  have hQp : IsPGroup p Q := ha.map _
  have hQK : Q ≤ K := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := hq
    have hy' : π y ∈ Subgroup.zpowers (π a) := by
      rw [← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem π hy
    have : π ((MulAut.conj g₁).toMonoidHom y) ∈
        (Subgroup.zpowers (π a)).map (MulAut.conj (π g₁)).toMonoidHom :=
      ⟨π y, hy', by simp⟩
    exact hg this
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p P K := hP.of_le hPK le_top
  obtain ⟨S, hS⟩ := (hQp.comap_subtype (K := K)).exists_le_sylow
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf p ((S : Subgroup K).map K.subtype) K := ⟨S, rfl⟩
  have hQS : Q ≤ (S : Subgroup K).map K.subtype := by
    intro q hq
    exact ⟨⟨q, hQK hq⟩, hS (show (⟨q, hQK hq⟩ : K) ∈ Q.comap K.subtype from hq), rfl⟩
  obtain ⟨k, hkK, hk⟩ := hPsyl.exists_mem_conj hSsyl
  obtain ⟨p₁, hp₁, hp₁k⟩ := hkK
  set r : H := k * p₁⁻¹ with hr
  have hrO : π r = 1 := by simp [hr, hp₁k]
  have h1 : g₁ * a * g₁⁻¹ ∈ (S : Subgroup K).map K.subtype :=
    hQS ⟨a, Subgroup.mem_zpowers a, by simp⟩
  have h2 : k⁻¹ * (g₁ * a * g₁⁻¹) * k ∈ P := (hk _).mp h1
  have h3 : (r⁻¹ * g₁) * a * (r⁻¹ * g₁)⁻¹ ∈ P := by
    have : (r⁻¹ * g₁) * a * (r⁻¹ * g₁)⁻¹ = p₁ * (k⁻¹ * (g₁ * a * g₁⁻¹) * k) * p₁⁻¹ := by
      simp only [hr]; group
    rw [this]
    exact P.mul_mem (P.mul_mem hp₁ h2) (P.inv_mem hp₁)
  have h4 := hwc (r⁻¹ * g₁) (by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact h3)
  have h5 : (r⁻¹ * g₁) * a * (r⁻¹ * g₁)⁻¹ ∈ Subgroup.zpowers a := by
    rw [← h4]
    exact ⟨a, Subgroup.mem_zpowers a, rfl⟩
  have h6 : π g₁ * π a * (π g₁)⁻¹ ∈ Subgroup.zpowers (π a) := by
    have := Subgroup.mem_map_of_mem π h5
    rw [MonoidHom.map_zpowers] at this
    simpa [map_mul, map_inv, hrO] using this
  exact map_conj_zpowers_eq_of_mem (π a) (π g₁) h6


private theorem sylow_subgroupOf {G : Type*} [Group G] [Finite G] [Fact p.Prime] (P : Sylow p G)
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M) :
    ∃ T : Sylow p M, (T : Subgroup M) = (P : Subgroup G).subgroupOf M := by
  have h : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) M := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hPM, P.isPGroup', fun h =>
      P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hPM))⟩
  exact h.exists_sylow_eq_subgroupOf

private theorem isSylowOf_top_subgroupOf {G : Type*} [Group G] [Finite G] [Fact p.Prime] (P : Sylow p G)
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G).subgroupOf M) (⊤ : Subgroup M) := by
  obtain ⟨T, hT⟩ := sylow_subgroupOf P hPM
  rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right, ← hT]
  exact ⟨le_top, T.isPGroup', T.not_dvd_index⟩

private theorem wc_subgroupOf {G : Type} [Group G] [Finite G] {M P : Subgroup G} {x : G} (hxM : x ∈ M)
    (hwc : U3LineWC x P) (g : ↥M)
    (hg : (Subgroup.zpowers (⟨x, hxM⟩ : M)).map (MulAut.conj g).toMonoidHom ≤ P.subgroupOf M) :
    (Subgroup.zpowers (⟨x, hxM⟩ : M)).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (⟨x, hxM⟩ : M) := by
  apply map_conj_zpowers_eq_of_mem
  have h1 : (g : G) * x * (g : G)⁻¹ ∈ P := hg ⟨⟨x, hxM⟩, Subgroup.mem_zpowers _, rfl⟩
  have h2 := hwc g (by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact h1)
  have h3 : (g : G) * x * (g : G)⁻¹ ∈ Subgroup.zpowers x := by
    rw [← h2]
    exact ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h3
  refine ⟨m, Subtype.ext ?_⟩
  simpa using hm

private theorem rank_quot {G : Type} [Group G] [Finite G] (hp : p.Prime) (M : Subgroup G)
    (hrank : CFSG.Open.pRank p M ≤ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p)) ≤ 3 := by
  have h1 := CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hp
    (primeComplementCore (G := ↥M) p) (primeComplementCore_coprime p) ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  exact hrank


private theorem centSeries_quot {G : Type} [Group G] [Finite G] (hp : p.Prime) {M P N : Subgroup G}
    {x : G} (hxM : x ∈ M) (hx : orderOf x = p)
    (hser : CentSeries p (M ⊓ Subgroup.centralizer ({x} : Set G)) P N) :
    ∃ N' : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p),
      CentSeries p (Subgroup.centralizer
          ({QuotientGroup.mk' (primeComplementCore (G := ↥M) p) ⟨x, hxM⟩} :
            Set (↥M ⧸ primeComplementCore (G := ↥M) p)))
        ((P.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p))) N' := by
  have hao : orderOf (⟨x, hxM⟩ : ↥M) = p := by rw [Subgroup.orderOf_mk]; exact hx
  have hPM : P ≤ M := fun y hy => (hser.P_le hy).1
  have hNM : N ≤ M := fun y hy => (hser.N_le hy).1
  have himg : ∀ c : ↥M, (c : G) ∈ Subgroup.centralizer ({x} : Set G) →
      QuotientGroup.mk' (primeComplementCore (G := ↥M) p) c ∈ Subgroup.centralizer
        ({QuotientGroup.mk' (primeComplementCore (G := ↥M) p) ⟨x, hxM⟩} :
          Set (↥M ⧸ primeComplementCore (G := ↥M) p)) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hc)
  have hlift : ∀ c ∈ Subgroup.centralizer
        ({QuotientGroup.mk' (primeComplementCore (G := ↥M) p) ⟨x, hxM⟩} :
          Set (↥M ⧸ primeComplementCore (G := ↥M) p)),
      ∃ c₀ : ↥M, (c₀ : G) ∈ M ⊓ Subgroup.centralizer ({x} : Set G) ∧
        QuotientGroup.mk' (primeComplementCore (G := ↥M) p) c₀ = c := by
    intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := centralizer_mk_le_map hp hao hc
    refine ⟨c₀, ⟨c₀.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc₀)
  refine ⟨((N.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p))), ?_⟩
  exact {
    P_le := by
      rintro _ ⟨c, hc, rfl⟩
      exact himg c (hser.P_le (show (c : G) ∈ P from hc)).2
    N_le := by
      rintro _ ⟨c, hc, rfl⟩
      exact himg c (hser.N_le (show (c : G) ∈ N from hc)).2
    N_norm := by
      intro c hc n hn
      obtain ⟨c₀, hc₀, rfl⟩ := hlift c hc
      obtain ⟨n₀, hn₀, rfl⟩ := hn
      refine ⟨c₀ * n₀ * c₀⁻¹, ?_, by simp⟩
      exact hser.N_norm (c₀ : G) hc₀ (n₀ : G) hn₀
    PN_norm := by
      intro c hc q hq
      obtain ⟨c₀, hc₀, rfl⟩ := hlift c hc
      have hPN : (P.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)) ⊔
          (N.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)) =
          ((P ⊔ N).subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)) := by
        rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hPM hNM]
      rw [hPN] at hq ⊢
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      exact ⟨c₀ * q₀ * c₀⁻¹, hser.PN_norm (c₀ : G) hc₀ (q₀ : G) hq₀, by simp⟩
    N_cop := by
      rintro _ ⟨n₀, hn₀, rfl⟩
      have h1 : orderOf (QuotientGroup.mk' (primeComplementCore (G := ↥M) p) n₀) ∣
          orderOf (n₀ : G) := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_map_dvd _ n₀
      exact Nat.Coprime.coprime_dvd_right h1 (hser.N_cop (n₀ : G) hn₀) }

private theorem PGroupDataAb.map_of_injOn {H Y : Type*} [Group H] [Group Y] (hp : p.Prime) (φ : H →* Y)
    {P T D : Subgroup H} {x : H} (hinj : Set.InjOn φ (P : Set H)) (h : PGroupDataAb p P T D x) :
    PGroupDataAb p (P.map φ) (T.map φ) (D.map φ) (φ x) where
  T_le := Subgroup.map_mono h.T_le
  D_le := Subgroup.map_mono h.D_le
  sup_eq := by rw [← Subgroup.map_sup, h.sup_eq]
  inf_eq := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨t, ht, rfl⟩, ⟨d, hd, hdt⟩⟩
    have htd : d = t := hinj (h.D_le hd) (h.T_le ht) hdt
    have : t ∈ T ⊓ D := ⟨ht, htd ▸ hd⟩
    rw [h.inf_eq, Subgroup.mem_bot] at this
    simp [this]
  comm := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul, h.comm t ht d hd]
  T_card := by
    rw [card_map_of_injOn' φ (hinj.mono (SetLike.coe_subset_coe.mpr h.T_le))]
    exact h.T_card
  T_exp := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, h.T_exp t ht, map_one]
  T_comm := by
    rw [isMulCommutative_iff_of_setLike]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, isMulCommutative_iff_of_setLike.mp h.T_comm a ha b hb]
  D_cyc := by
    haveI := h.D_cyc
    exact isCyclic_of_surjective (φ.subgroupMap D) (φ.subgroupMap_surjective D)
  x_mem := Subgroup.mem_map_of_mem φ h.x_mem
  x_ord := by
    have hxP : x ∈ P := h.D_le h.x_mem
    have hdvd : orderOf (φ x) ∣ p := h.x_ord ▸ orderOf_map_dvd φ x
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exfalso
      have h1' : φ x = 1 := orderOf_eq_one_iff.mp h1
      have : x = 1 := hinj hxP P.one_mem (by rw [h1', map_one])
      have h2 : orderOf x = 1 := orderOf_eq_one_iff.mpr this
      rw [h.x_ord] at h2
      exact hp.ne_one h2
    · exact h1

private theorem PGroupDataAb.subgroupOf {G : Type*} [Group G] {P T D : Subgroup G} {x : G}
    (M : Subgroup G) (hPM : P ≤ M) (hxM : x ∈ M) (h : PGroupDataAb p P T D x) :
    PGroupDataAb p (P.subgroupOf M) (T.subgroupOf M) (D.subgroupOf M) (⟨x, hxM⟩ : M) where
  T_le := fun a ha => h.T_le ha
  D_le := fun a ha => h.D_le ha
  sup_eq := by
    rw [← Subgroup.subgroupOf_sup (h.T_le.trans hPM) (h.D_le.trans hPM), h.sup_eq]
  inf_eq := by
    rw [eq_bot_iff]
    intro a ha
    have : (a : G) ∈ T ⊓ D := ⟨ha.1, ha.2⟩
    rw [h.inf_eq, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  comm := fun t ht d hd => Subtype.ext (h.comm t ht d hd)
  T_card := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.T_le.trans hPM)).toEquiv]
    exact h.T_card
  T_exp := fun t ht => Subtype.ext (by simpa using h.T_exp t ht)
  T_comm := by
    rw [isMulCommutative_iff_of_setLike]
    intro a ha b hb
    have := isMulCommutative_iff_of_setLike.mp h.T_comm a ha b hb
    exact Subtype.ext this
  D_cyc := by
    have := h.D_cyc
    exact (Subgroup.subgroupOfEquivOfLe (h.D_le.trans hPM)).symm.isCyclic.mp h.D_cyc
  x_mem := h.x_mem
  x_ord := by
    rw [Subgroup.orderOf_mk]
    exact h.x_ord

end Generic

theorem case2Data_of_G {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Open.IsKProper G) {P : Sylow p G} {M : Subgroup G} (hMtop : M ≠ ⊤)
    (hPM : (P : Subgroup G) ≤ M) (hrank : CFSG.Open.pRank p M ≤ 3)
    {x : G} (hxM : x ∈ M) {T D F N : Subgroup G}
    (hpd : PGroupData p (P : Subgroup G) T D x) (hF : TorusProps p T F) (hFM : F ≤ M)
    (hFD : ∀ f ∈ F, ∀ d ∈ D, f * d * f⁻¹ = d)
    (hser : CentSeries p (M ⊓ Subgroup.centralizer ({x} : Set G)) (P : Subgroup G) N)
    (hwc : U3LineWC x (P : Subgroup G)) :
    Case2Data p
      (((P : Subgroup G).subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)))
      ((T.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)))
      ((D.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)))
      ((F.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)))
      (QuotientGroup.mk' (primeComplementCore (G := ↥M) p) ⟨x, hxM⟩) := by
  have hp : p.Prime := Fact.out
  have hTP : T ≤ (P : Subgroup G) := hpd.T_le
  have hTM : T ≤ M := hTP.trans hPM
  have hPp : IsPGroup p ((P : Subgroup G).subgroupOf M) := P.isPGroup'.comap_subtype
  have hinj : Set.InjOn (QuotientGroup.mk' (primeComplementCore (G := ↥M) p))
      (((P : Subgroup G).subgroupOf M : Subgroup ↥M) : Set ↥M) :=
    injOn_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hPp
  have hpd' := PGroupData.subgroupOf M hPM hxM hpd
  have hF' := TorusProps.subgroupOf M hTM hFM hF
  have hTinj : Set.InjOn (QuotientGroup.mk' (primeComplementCore (G := ↥M) p))
      ((T.subgroupOf M : Subgroup ↥M) : Set ↥M) := hinj.mono (fun a ha => hTP ha)
  have hx : orderOf x = p := hpd.x_ord
  have hao : orderOf (⟨x, hxM⟩ : ↥M) = p := by rw [Subgroup.orderOf_mk]; exact hx
  refine
    { prime := hp
      five := hp5
      core := primeComplementCore_quotient_eq_bot p
      catalog := (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hK M hMtop).quotient _
      rank := rank_quot hp M hrank
      sylow := ?_
      pdata := PGroupData.map_of_injOn hp _ hinj hpd'
      torus := TorusProps.map_of_injOn _ hTinj hF'
      F_D := ?_
      series := centSeries_quot hp hxM hx hser
      wc := ?_ }
  · obtain ⟨T', hT'⟩ := sylow_subgroupOf P hPM
    exact ⟨T'.mapSurjective (QuotientGroup.mk'_surjective _), by rw [Sylow.coe_mapSurjective, hT']⟩
  · rintro _ ⟨f, hf, rfl⟩ _ ⟨d, hd, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hFD f hf d hd))
  · intro g hg
    have ha : IsPGroup p (Subgroup.zpowers (⟨x, hxM⟩ : ↥M)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
    exact weaklyClosed_map_mk_of_sylow _ (isSylowOf_top_subgroupOf P hPM) ha
      (fun g' hg' => wc_subgroupOf hxM hwc g' hg') g hg

theorem case2DataAb_of_G {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Open.IsKProper G) {P : Sylow p G} {M : Subgroup G} (hMtop : M ≠ ⊤)
    (hPM : (P : Subgroup G) ≤ M) (hrank : CFSG.Open.pRank p M ≤ 3)
    {x : G} (hxM : x ∈ M) {T D F N : Subgroup G}
    (hpd : PGroupDataAb p (P : Subgroup G) T D x) (hFM : F ≤ M)
    (hFT : ∀ f ∈ F, ∀ t ∈ T, f * t * f⁻¹ ∈ T)
    (hFtrans : ∀ a ∈ T, a ≠ 1 → ∀ b ∈ T, b ≠ 1 → ∃ f ∈ F, f * a * f⁻¹ = b)
    (hser : CentSeries p (M ⊓ Subgroup.centralizer ({x} : Set G)) (P : Subgroup G) N)
    (hwc : U3LineWC x (P : Subgroup G)) :
    Case2DataAb p
      (((P : Subgroup G).subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)))
      ((T.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)))
      ((D.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)))
      ((F.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)))
      (QuotientGroup.mk' (primeComplementCore (G := ↥M) p) ⟨x, hxM⟩) := by
  have hp : p.Prime := Fact.out
  have hTP : T ≤ (P : Subgroup G) := hpd.T_le
  have hPp : IsPGroup p ((P : Subgroup G).subgroupOf M) := P.isPGroup'.comap_subtype
  have hinj : Set.InjOn (QuotientGroup.mk' (primeComplementCore (G := ↥M) p))
      (((P : Subgroup G).subgroupOf M : Subgroup ↥M) : Set ↥M) :=
    injOn_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hPp
  have hpd' := PGroupDataAb.subgroupOf M hPM hxM hpd
  have hx : orderOf x = p := hpd.x_ord
  have hao : orderOf (⟨x, hxM⟩ : ↥M) = p := by rw [Subgroup.orderOf_mk]; exact hx
  refine
    { prime := hp
      five := hp5
      core := primeComplementCore_quotient_eq_bot p
      catalog := (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hK M hMtop).quotient _
      rank := rank_quot hp M hrank
      sylow := ?_
      pdata := PGroupDataAb.map_of_injOn hp _ hinj hpd'
      F_T := ?_
      F_trans := ?_
      series := centSeries_quot hp hxM hx hser
      wc := ?_ }
  · obtain ⟨T', hT'⟩ := sylow_subgroupOf P hPM
    exact ⟨T'.mapSurjective (QuotientGroup.mk'_surjective _), by rw [Sylow.coe_mapSurjective, hT']⟩
  · rintro _ ⟨f, hf, rfl⟩ _ ⟨t, ht, rfl⟩
    refine ⟨f * t * f⁻¹, ?_, by simp⟩
    exact hFT (f : G) hf (t : G) ht
  · rintro _ ⟨a, ha, rfl⟩ ha1 _ ⟨b, hb, rfl⟩ hb1
    have ha1' : (a : G) ≠ 1 := by
      intro h
      apply ha1
      have h' : a = 1 := Subtype.ext h
      rw [h', map_one]
    have hb1' : (b : G) ≠ 1 := by
      intro h
      apply hb1
      have h' : b = 1 := Subtype.ext h
      rw [h', map_one]
    obtain ⟨f, hf, hfab⟩ := hFtrans (a : G) ha ha1' (b : G) hb hb1'
    refine ⟨QuotientGroup.mk' (primeComplementCore (G := ↥M) p) ⟨f, hFM hf⟩,
      ⟨⟨f, hFM hf⟩, hf, rfl⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hfab)
  · intro g hg
    have ha : IsPGroup p (Subgroup.zpowers (⟨x, hxM⟩ : ↥M)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
    exact weaklyClosed_map_mk_of_sylow _ (isSylowOf_top_subgroupOf P hPM) ha
      (fun g' hg' => wc_subgroupOf hxM hwc g' hg') g hg

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
