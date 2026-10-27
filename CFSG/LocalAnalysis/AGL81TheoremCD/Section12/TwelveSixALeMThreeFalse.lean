module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMTools
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMStepZero
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpPrimeCoreLe
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenTrans
import CFSG.GroupTheory.PrimeOrderSubgroupCount
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixWConj

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private structure StarPreimageData (H : Subgroup G) where
  R : Subgroup G
  le : R ≤ H
  subgroupOf_eq : R.subgroupOf H = (CFSG.pCore 3 (StarGroup 3 H)).comap
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3))
  normal : (R.subgroupOf H).Normal
  le_normalizer : H ≤ Subgroup.normalizer (R : Set G)
  relPPrimeCore_le : relPPrimeCore 3 H ≤ R
  starImg_eq : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H)
  isPGroup_starImg : IsPGroup 3 ↥(starImg 3 H R)


private theorem exists_mul_mul_of_mem_sup {X : Type*} [Group X] {A B C : Subgroup X}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) {x : X} (hx : x ∈ A ⊔ B ⊔ C) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, x = a * b * c := by
  have hAB_C : ∀ y ∈ A ⊔ B, ∀ c ∈ C, y * c = c * y := by
    intro y hy c hc
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hAB hy
    calc a * b * c = a * (b * c) := by group
      _ = a * (c * b) := by rw [hBC b hb c hc]
      _ = a * c * b := by group
      _ = c * a * b := by rw [hAC a ha c hc]
      _ = c * (a * b) := by group
  obtain ⟨y, hy, c, hc, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hAB_C hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hAB hy
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

private theorem mulAut_fix_of_fixes_sup {X : Type} [Group X] {A B : Subgroup X}
    {φ : MulAut X} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : ∀ x ∈ A, φ x = x) (hB : ∀ x ∈ B, φ x = x) :
    ∀ x ∈ A ⊔ B, φ x = x := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hAB hx
  rw [map_mul, hA a ha, hB b hb]

private theorem commute_of_conj_eq {X : Type} [Group X] {t x : X}
    (h : t * x * t⁻¹ = x) : t * x = x * t := by
  calc t * x = t * x * t⁻¹ * t := by group
    _ = x * t := by rw [h]

private theorem mulAut_eq_of_agree_sup {X : Type*} [Group X] {A B C : Subgroup X}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (f g : MulAut X) (hA : ∀ x ∈ A, f x = g x) (hB : ∀ x ∈ B, f x = g x)
    (hC : ∀ x ∈ C, f x = g x) {x : X} (hx : x ∈ A ⊔ B ⊔ C) : f x = g x := by
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ :=
    exists_mul_mul_of_mem_sup hAB hAC hBC hx
  rw [map_mul, map_mul, map_mul, map_mul, hA a ha, hB b hb, hC c hc]


private theorem IsE27InvConfig.eq_W_of_invariant_two
    {X : Type} [Group X] [Finite X] {V W₁ W₂ W₃ : Subgroup X} {t₁ t₂ t₃ : X}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃)
    {D : Subgroup X} (hDV : D ≤ V) (hDcard : Nat.card D = 3)
    (hD1 : ∀ x ∈ D, t₁ * x * t₁⁻¹ ∈ D) (hD2 : ∀ x ∈ D, t₂ * x * t₂⁻¹ ∈ D) :
    D = W₁ ∨ D = W₂ ∨ D = W₃ := by
  classical
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDcard
    omega
  have hD1inv : ∀ x ∈ D, t₁⁻¹ * x * t₁ ∈ D :=
    CFSG.Quasithin.Vol2.Ch11.G2Q8.inv_conj_mem_of_conj_mem' hD1
  have hD2inv : ∀ x ∈ D, t₂⁻¹ * x * t₂ ∈ D :=
    CFSG.Quasithin.Vol2.Ch11.G2Q8.inv_conj_mem_of_conj_mem' hD2
  have hD3 : ∀ x ∈ D, t₃ * x * t₃⁻¹ ∈ D := by
    intro x hx
    have hτ : (t₁ * t₂ * t₃) * x * (t₁ * t₂ * t₃)⁻¹ ∈ D := by
      rw [h.conj_mul_mul_eq_inv (hDV hx)]
      exact D.inv_mem hx
    have h1 : t₁⁻¹ * ((t₁ * t₂ * t₃) * x * (t₁ * t₂ * t₃)⁻¹) * t₁ ∈ D :=
      hD1inv _ hτ
    have h2 : t₂⁻¹ * (t₁⁻¹ * ((t₁ * t₂ * t₃) * x * (t₁ * t₂ * t₃)⁻¹) * t₁) * t₂ ∈ D :=
      hD2inv _ h1
    have ht3 : t₃ = t₂⁻¹ * t₁⁻¹ * (t₁ * t₂ * t₃) := by group
    rw [ht3]
    have hgoal : t₂⁻¹ * t₁⁻¹ * (t₁ * t₂ * t₃) * x *
          (t₂⁻¹ * t₁⁻¹ * (t₁ * t₂ * t₃))⁻¹ =
        t₂⁻¹ * (t₁⁻¹ * ((t₁ * t₂ * t₃) * x * (t₁ * t₂ * t₃)⁻¹) * t₁) * t₂ := by
      group
    rw [hgoal]
    exact h2
  have hDt : ∀ t ∈ ({t₁, t₂, t₃} : Set X), ∀ x ∈ D, t * x * t⁻¹ ∈ D := by
    intro t ht x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact hD1 x hx
    · exact hD2 x hx
    · exact hD3 x hx
  rcases h.exists_le_of_invariant hDV hDne hDt with h1 | h2 | h3
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h1 (by rw [hDcard, h.card₁])).symm
  · exact Or.inr (Or.inl (Subgroup.eq_of_le_of_card_ge h2 (by rw [hDcard, h.card₂])).symm)
  · exact Or.inr (Or.inr (Subgroup.eq_of_le_of_card_ge h3 (by rw [hDcard, h.card₃])).symm)

private theorem starPreimageData_exists (H : Subgroup G) :
    Nonempty (StarPreimageData H) := by
  let R : Subgroup G := ((CFSG.pCore 3 (StarGroup 3 H)).comap
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3))).map H.subtype
  have hRH : R ≤ H := Subgroup.map_subtype_le _
  have hRsub : R.subgroupOf H = (CFSG.pCore 3 (StarGroup 3 H)).comap
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)) := by
    dsimp [R]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hRnorm : (R.subgroupOf H).Normal := by
    rw [hRsub]
    infer_instance
  have hHN : H ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mp hRnorm
  have hOleR : relPPrimeCore 3 H ≤ R := by
    rw [nineTenGen_relPPrimeCore_eq_map Nat.prime_three H]
    dsimp [R]
    refine Subgroup.map_mono ?_
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact (CFSG.pCore 3 (StarGroup 3 H)).one_mem
  have hstarR : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H) := by
    dsimp only [starImg, R, Subgroup.subgroupOf]
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact ⟨⟨R, hRH, hRsub, hRnorm, hHN, hOleR, hstarR,
    by rw [hstarR]; exact CFSG.pCore_isPGroup⟩⟩

private theorem isSylowOf_starImg_of_isSylowOf
    {V : Subgroup G} (hV : CFSG.ABGLocalTools.IsSylowOf 3 V H) :
    ∃ S : Sylow 3 (StarGroup 3 H), (S : Subgroup (StarGroup 3 H)) = starImg 3 H V := by
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) 3
  let π : ↥H →* StarGroup 3 H := QuotientGroup.mk' O
  obtain ⟨S, hS⟩ := hV.exists_sylow_eq_subgroupOf
  refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective O), ?_⟩
  rw [Sylow.coe_mapSurjective, hS]
  rfl


private structure SetupData (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1) where
  V : Subgroup G
  R : Subgroup G
  hVsyl : CFSG.ABGLocalTools.IsSylowOf 3 V (H ⊓ M)
  hVsylH : CFSG.ABGLocalTools.IsSylowOf 3 V H
  hV3 : IsPGroup 3 V
  hVM : V ≤ M
  hVHM : V ≤ H ⊓ M
  hV0V : D.V ≤ V
  hRH : R ≤ H
  hRsub : R.subgroupOf H = (CFSG.pCore 3 (StarGroup 3 H)).comap
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3))
  hRnorm : (R.subgroupOf H).Normal
  hHN : H ≤ Subgroup.normalizer (R : Set G)
  hOleR : relPPrimeCore 3 H ≤ R
  hstarR : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H)
  hUp : IsPGroup 3 ↥(starImg 3 H R)
  hRsup : R ≤ relPPrimeCore 3 H ⊔ (V ⊓ R)
  hV0star : starImg 3 H D.V ≤ CFSG.pCore 3 (StarGroup 3 H)
  hV0R : D.V ≤ R

private theorem setupData_exists
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hp : p = 3)
    (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    (hY : starImg p H D.I₁ ≤ cStarL p H ∧ starImg p H D.I₂ ≤ cStarL p H ∧
      starImg p H D.I₃ ≤ cStarL p H) :
    Nonempty (SetupData hc D hn) := by
  subst p
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := hc.ctx.exists_E_sq
  have hd : NineSettingGen G M 3 E H E 2 :=
    (hc.ctx.hypCGen hEQ hE hEc hΓ).toNineSettingGen
  have hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hc.ctx.p_not_mem_sigma
  have hU : NineNineOne M 3 := hc.hI G M E H E 3 hd hpσ
  have hDVHM : D.V ≤ H ⊓ M := D.V_le.trans (D.sup_le hc.data)
  have hDVH : D.V ≤ H := hDVHM.trans inf_le_left
  obtain ⟨V, hVsyl, hV0V⟩ :=
    exists_isSylowOf_ge hDVHM (CFSG.Open.IsElemAbelian.isPGroup D.cfg.elem)
  have hVsylH : CFSG.ABGLocalTools.IsSylowOf 3 V H :=
    (isSylowOf_of_NineNineOne hc.ctx.maxLocal hc.ctx.mem_QSet hc.ctx.Q_le_H hpσ hU hVsyl).1
  have hV3 : IsPGroup 3 V := hVsylH.isPGroup
  have hVM : V ≤ M := hVsyl.le.trans inf_le_right
  obtain ⟨Rdata⟩ := starPreimageData_exists (G := G) H
  let R := Rdata.R
  have hRH : R ≤ H := Rdata.le
  have hRsub : R.subgroupOf H = (CFSG.pCore 3 (StarGroup 3 H)).comap
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)) := Rdata.subgroupOf_eq
  have hRnorm : (R.subgroupOf H).Normal := Rdata.normal
  have hHN : H ≤ Subgroup.normalizer (R : Set G) := Rdata.le_normalizer
  have hOleR : relPPrimeCore 3 H ≤ R := Rdata.relPPrimeCore_le
  have hstarR : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H) := Rdata.starImg_eq
  have hUp : IsPGroup 3 ↥(starImg 3 H R) := Rdata.isPGroup_starImg
  have hS' : CFSG.ABGLocalTools.IsSylowOf 3 (V ⊓ R) R :=
    hVsylH.inf_of_le_normalizer hRH hHN
  have hRsup : R ≤ relPPrimeCore 3 H ⊔ (V ⊓ R) :=
    nineTenGen_le_sup_of_starImg_isPGroup Nat.prime_three hRH hOleR hUp hS'
  have hV0star : starImg 3 H D.V ≤ CFSG.pCore 3 (StarGroup 3 H) :=
    hc.starImg_V_le_pCore D rfl hn hY
  have hV0R : D.V ≤ R := by
    have hle : D.V ≤ R ⊔ relPPrimeCore 3 H :=
      le_sup_relPPrimeCore_of_starImg_le Nat.prime_three hDVH (by rw [hstarR]; exact hV0star)
    exact hle.trans (sup_le le_rfl hOleR)
  exact ⟨⟨V, R, hVsyl, hVsylH, hV3, hVM, hVsyl.le, hV0V, hRH, hRsub, hRnorm, hHN,
    hOleR, hstarR, hUp, hRsup, hV0star, hV0R⟩⟩

private theorem inf_eq_V0_of_not_le
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    {V R : Subgroup G} (hV3 : IsPGroup 3 V) (hVM : V ≤ M) (hV0V : D.V ≤ V)
    (hV0R : D.V ≤ R) (hnot : ¬ V ≤ R) : V ⊓ R = D.V := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV0le : D.V ≤ V ⊓ R := le_inf hV0V hV0R
  have hcardV_le : Nat.card V ≤ 81 :=
    TwelveFiveData.card_le_eighty_one hc.data hn hc.h3 hc.hcard hVM hV3
  let VR : Subgroup G := V ⊓ R
  have h3 : IsPGroup 3 VR := hV3.to_le (H := VR) (K := V) inf_le_left
  obtain ⟨n, hncard⟩ := h3.exists_card_eq
  have h27le : 27 ≤ Nat.card VR := by
    rw [← D.cfg.card]
    exact Subgroup.card_le_of_le hV0le
  have hcard_le' : Nat.card VR ≤ 81 :=
    (Subgroup.card_le_of_le inf_le_left).trans hcardV_le
  have h3le : 3 ≤ n := by
    have h : 3 ^ 3 ≤ 3 ^ n := by rw [← hncard]; norm_num at h27le ⊢; exact h27le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
  have hnle : n ≤ 4 := by
    have h : 3 ^ n ≤ 3 ^ 4 := by rw [← hncard]; norm_num at hcard_le' ⊢; exact hcard_le'
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
  have hn3 : n = 3 := by
    by_contra hne
    have h4 : n = 4 := by omega
    have hcardVR : Nat.card VR = 81 := by rw [hncard, h4]; norm_num
    have hcardV : Nat.card V = 81 :=
      le_antisymm hcardV_le (by
        rw [← hcardVR]
        exact Subgroup.card_le_of_le inf_le_left)
    have hVR_eq : VR = V :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardV, hcardVR])
    exact hnot (by rw [← hVR_eq]; exact inf_le_right)
  have hcard : Nat.card VR = 27 := by
    rw [hncard, hn3]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hV0le (by rw [hcard, D.cfg.card])).symm

private theorem pCore_le_starImg_V0_of_inf_le
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {V R : Subgroup G} (hRsup : R ≤ relPPrimeCore 3 H ⊔ (V ⊓ R))
    (hstarR : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H))
    (hle : V ⊓ R ≤ D.V) :
    CFSG.pCore 3 (StarGroup 3 H) ≤ starImg 3 H D.V := by
  have hDVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  have hOH : relPPrimeCore 3 H ≤ H := sSup_le fun N hN => hN.1
  have hRle : R ≤ relPPrimeCore 3 H ⊔ D.V :=
    hRsup.trans (sup_le le_sup_left (hle.trans le_sup_right))
  have hstarO : starImg 3 H (relPPrimeCore 3 H) = ⊥ := by
    rw [nineTenGen_relPPrimeCore_eq_map Nat.prime_three H]
    dsimp only [starImg, Subgroup.subgroupOf]
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hsup : starImg 3 H (relPPrimeCore 3 H ⊔ D.V) =
      starImg 3 H (relPPrimeCore 3 H) ⊔ starImg 3 H D.V := by
    unfold starImg
    rw [Subgroup.subgroupOf_sup hOH hDVH, Subgroup.map_sup]
  have hmono : starImg 3 H R ≤ starImg 3 H (relPPrimeCore 3 H ⊔ D.V) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (hRle (Subgroup.mem_subgroupOf.mp hy)))
  calc CFSG.pCore 3 (StarGroup 3 H) = starImg 3 H R := hstarR.symm
    _ ≤ starImg 3 H (relPPrimeCore 3 H ⊔ D.V) := hmono
    _ = starImg 3 H (relPPrimeCore 3 H) ⊔ starImg 3 H D.V := hsup
    _ = ⊥ ⊔ starImg 3 H D.V := by rw [hstarO]
    _ = starImg 3 H D.V := bot_sup_eq _


private theorem starImg_sup_of_le {A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    starImg 3 H (A ⊔ B) = starImg 3 H A ⊔ starImg 3 H B := by
  unfold starImg
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

private theorem conjNormal_fix_of_comm {t : G} (ht : t ∈ H) {W : Subgroup G} (hWH : W ≤ H)
    (hcomm : ∀ w ∈ W, t * w = w * t)
    (x : ↥(CFSG.pCore 3 (StarGroup 3 H)))
    (hx : (x : StarGroup 3 H) ∈ starImg 3 H W) :
    MulAut.conjNormal (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨t, ht⟩) x = x := by
  classical
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) 3
  let π : ↥H →* StarGroup 3 H := QuotientGroup.mk' O
  let tH : ↥H := ⟨t, ht⟩
  let tbar : StarGroup 3 H := π tH
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
  have hyW : (y : G) ∈ W := Subgroup.mem_subgroupOf.mp hy
  have hconj : tH * y * tH⁻¹ = y := by
    apply Subtype.ext
    calc t * (y : G) * t⁻¹ = ((y : G) * t) * t⁻¹ := by rw [hcomm (y : G) hyW]
      _ = (y : G) := by group
  have hmap := congrArg π hconj
  have hxval : (x : StarGroup 3 H) = π y := hxy.symm
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  change tbar * (x : StarGroup 3 H) * tbar⁻¹ = (x : StarGroup 3 H)
  rw [hxval]
  have hmap' : π tH * π y * (π tH)⁻¹ = π y := by
    simpa only [map_mul, map_inv] using hmap
  simpa [tbar, tH, π] using hmap'

private theorem conjNormal_inv_of_inv {t : G} (ht : t ∈ H) {W : Subgroup G} (hWH : W ≤ H)
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)
    (x : ↥(CFSG.pCore 3 (StarGroup 3 H)))
    (hx : (x : StarGroup 3 H) ∈ starImg 3 H W) :
    MulAut.conjNormal (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨t, ht⟩) x = x⁻¹ := by
  classical
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) 3
  let π : ↥H →* StarGroup 3 H := QuotientGroup.mk' O
  let tH : ↥H := ⟨t, ht⟩
  let tbar : StarGroup 3 H := π tH
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
  have hyW : (y : G) ∈ W := Subgroup.mem_subgroupOf.mp hy
  have hconj : tH * y * tH⁻¹ = ⟨(y : G)⁻¹, H.inv_mem y.2⟩ := by
    apply Subtype.ext
    exact hinv (y : G) hyW
  have hmap := congrArg π hconj
  have hxval : (x : StarGroup 3 H) = π y := hxy.symm
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  change tbar * (x : StarGroup 3 H) * tbar⁻¹ =
    ((x⁻¹ : ↥(CFSG.pCore 3 (StarGroup 3 H))) : StarGroup 3 H)
  rw [hxval]
  have hxinv : ((x⁻¹ : ↥(CFSG.pCore 3 (StarGroup 3 H))) : StarGroup 3 H) = (π y)⁻¹ := by
    rw [← hxval]
    rfl
  rw [hxinv]
  have hmap' : π tH * π y * (π tH)⁻¹ =
      π (⟨(y : G)⁻¹, H.inv_mem y.2⟩ : ↥H) := by
    simpa only [map_mul, map_inv] using hmap
  rw [show (π y)⁻¹ = π (⟨(y : G)⁻¹, H.inv_mem y.2⟩ : ↥H) by
    rw [← map_inv]
    rfl]
  simpa [tbar, tH, π] using hmap' 


private theorem starImg_V_eq_sup_W
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hRstar : CFSG.pCore 3 (StarGroup 3 H) = starImg 3 H D.V) :
    CFSG.pCore 3 (StarGroup 3 H) =
      starImg 3 H D.W₁ ⊔ starImg 3 H D.W₂ ⊔ starImg 3 H D.W₃ := by
  have hW1H : D.W₁ ≤ H := D.le₁.trans (D.le_inf₁.trans inf_le_left)
  have hW2H : D.W₂ ≤ H := D.le₂.trans (D.le_inf₂.trans inf_le_left)
  have hW3H : D.W₃ ≤ H := D.le₃.trans (D.le_inf₃.trans inf_le_left)
  rw [hRstar, D.cfg.join]
  rw [starImg_sup_of_le (A := D.W₁ ⊔ D.W₂) (B := D.W₃) (sup_le hW1H hW2H) hW3H,
    starImg_sup_of_le hW1H hW2H]

private theorem W_le_H_and_DV (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    (D.W₁ ≤ H ∧ D.W₂ ≤ H ∧ D.W₃ ≤ H) ∧
      (D.W₁ ≤ D.V ∧ D.W₂ ≤ D.V ∧ D.W₃ ≤ D.V) := by
  have hW1H : D.W₁ ≤ H := D.le₁.trans (D.le_inf₁.trans inf_le_left)
  have hW2H : D.W₂ ≤ H := D.le₂.trans (D.le_inf₂.trans inf_le_left)
  have hW3H : D.W₃ ≤ H := D.le₃.trans (D.le_inf₃.trans inf_le_left)
  refine ⟨⟨hW1H, hW2H, hW3H⟩, ?_, ?_, ?_⟩
  · rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  · rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  · rw [D.cfg.join]; exact le_sup_right

private theorem starImg_W_le_pCore
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hRstar : starImg 3 H D.V = CFSG.pCore 3 (StarGroup 3 H)) :
    starImg 3 H D.W₁ ≤ CFSG.pCore 3 (StarGroup 3 H) ∧
      starImg 3 H D.W₂ ≤ CFSG.pCore 3 (StarGroup 3 H) ∧
      starImg 3 H D.W₃ ≤ CFSG.pCore 3 (StarGroup 3 H) := by
  obtain ⟨-, hW1DV, hW2DV, hW3DV⟩ := W_le_H_and_DV D
  refine ⟨?_, ?_, ?_⟩
  · rw [← hRstar]; exact Subgroup.map_mono (Subgroup.comap_mono hW1DV)
  · rw [← hRstar]; exact Subgroup.map_mono (Subgroup.comap_mono hW2DV)
  · rw [← hRstar]; exact Subgroup.map_mono (Subgroup.comap_mono hW3DV)

private theorem starImg_W_card (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    Nat.card (starImg 3 H D.W₁) = 3 ∧ Nat.card (starImg 3 H D.W₂) = 3 ∧
      Nat.card (starImg 3 H D.W₃) = 3 := by
  obtain ⟨⟨hW1H, hW2H, hW3H⟩, -⟩ := W_le_H_and_DV D
  have hW1_3 : IsPGroup 3 D.W₁ := IsPGroup.of_card (n := 1) (by rw [D.cfg.card₁]; norm_num)
  have hW2_3 : IsPGroup 3 D.W₂ := IsPGroup.of_card (n := 1) (by rw [D.cfg.card₂]; norm_num)
  have hW3_3 : IsPGroup 3 D.W₃ := IsPGroup.of_card (n := 1) (by rw [D.cfg.card₃]; norm_num)
  exact ⟨by rw [card_starImg_eq Nat.prime_three hW1H hW1_3, D.cfg.card₁],
    by rw [card_starImg_eq Nat.prime_three hW2H hW2_3, D.cfg.card₂],
    by rw [card_starImg_eq Nat.prime_three hW3H hW3_3, D.cfg.card₃]⟩

private theorem starImg_elem_card
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hRstar : starImg 3 H D.V = CFSG.pCore 3 (StarGroup 3 H)) :
    IsElemAbelian 3 (CFSG.pCore 3 (StarGroup 3 H)) ∧
      Nat.card (CFSG.pCore 3 (StarGroup 3 H)) = 27 := by
  have helem : IsElemAbelian 3 (CFSG.pCore 3 (StarGroup 3 H)) := by
    rw [← hRstar]
    exact (D.cfg.elem.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3))
  have hcardR : Nat.card (CFSG.pCore 3 (StarGroup 3 H)) = 27 := by
    rw [← hRstar, card_starImg_eq Nat.prime_three
      (D.V_le.trans (D.sup_le hc.data) |>.trans inf_le_left)
      (CFSG.Open.IsElemAbelian.isPGroup D.cfg.elem), D.cfg.card]
  exact ⟨helem, hcardR⟩

private theorem starImg_conjNormal_inv
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hRstar : starImg 3 H D.V = CFSG.pCore 3 (StarGroup 3 H))
    {t : G} (ht : t ∈ H) {W : Subgroup G} (hWH : W ≤ H) (hWV : W ≤ D.V)
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) :
    ∀ x ∈ starImg 3 H W,
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨t, ht⟩) * x *
          (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨t, ht⟩)⁻¹ = x⁻¹ := by
  intro x hx
  have hWP : starImg 3 H W ≤ CFSG.pCore 3 (StarGroup 3 H) := by
    rw [← hRstar]
    exact Subgroup.map_mono (Subgroup.comap_mono hWV)
  have h := conjNormal_inv_of_inv (t := t) ht hWH hinv
    (⟨x, hWP hx⟩ : ↥(CFSG.pCore 3 (StarGroup 3 H))) hx
  have h2 := congrArg (fun z : ↥(CFSG.pCore 3 (StarGroup 3 H)) =>
    (z : StarGroup 3 H)) h
  simpa [MulAut.conjNormal_apply] using h2

private theorem starImg_conjNormal_fix
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hRstar : starImg 3 H D.V = CFSG.pCore 3 (StarGroup 3 H))
    {t : G} (ht : t ∈ H) {W : Subgroup G} (hWH : W ≤ H) (hWV : W ≤ D.V)
    (hcomm : ∀ w ∈ W, t * w = w * t) :
    ∀ x ∈ starImg 3 H W,
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨t, ht⟩) * x *
          (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨t, ht⟩)⁻¹ = x := by
  intro x hx
  have hWP : starImg 3 H W ≤ CFSG.pCore 3 (StarGroup 3 H) := by
    rw [← hRstar]
    exact Subgroup.map_mono (Subgroup.comap_mono hWV)
  have h := conjNormal_fix_of_comm (t := t) ht hWH hcomm
    (⟨x, hWP hx⟩ : ↥(CFSG.pCore 3 (StarGroup 3 H))) hx
  have h2 := congrArg (fun z : ↥(CFSG.pCore 3 (StarGroup 3 H)) =>
    (z : StarGroup 3 H)) h
  simpa [MulAut.conjNormal_apply] using h2

private theorem conj_comm_of_mem_sup {X : Type} [Group X] {t : X} {A B : Subgroup X}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : ∀ x ∈ A, t * x * t⁻¹ = x) (hB : ∀ x ∈ B, t * x * t⁻¹ = x) :
    ∀ x ∈ A ⊔ B, t * x = x * t := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hAB hx
  calc t * (a * b) = (t * a) * b := by group
    _ = (a * t) * b := by rw [commute_of_conj_eq (hA a ha)]
    _ = a * (t * b) := by group
    _ = a * (b * t) := by rw [commute_of_conj_eq (hB b hb)]
    _ = (a * b) * t := by group

private theorem elemAbelian_mul_comm {P : Subgroup (StarGroup 3 H)}
    (helem : IsElemAbelian 3 P) :
    ∀ a b : StarGroup 3 H, a ∈ P → b ∈ P → a * b = b * a := by
  intro a b ha hb
  haveI : IsMulCommutative ↥P := helem.1
  have h := setLike_mul_comm
    (show (⟨a, ha⟩ : ↥P) ∈ (⊤ : Subgroup ↥P) from Subgroup.mem_top _)
    (show (⟨b, hb⟩ : ↥P) ∈ (⊤ : Subgroup ↥P) from Subgroup.mem_top _)
  exact congrArg Subtype.val h

private theorem isE27InvConfig_star
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hRstar : starImg 3 H D.V = CFSG.pCore 3 (StarGroup 3 H)) :
    IsE27InvConfig (CFSG.pCore 3 (StarGroup 3 H))
      (starImg 3 H D.W₁) (starImg 3 H D.W₂) (starImg 3 H D.W₃)
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨D.t₁, (D.t₁_mem hc.data).1⟩)
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨D.t₂, (D.t₂_mem hc.data).1⟩)
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨D.t₃, (D.t₃_mem hc.data).1⟩) := by
  classical
  obtain ⟨⟨hW1H, hW2H, hW3H⟩, hW1DV, hW2DV, hW3DV⟩ := W_le_H_and_DV D
  obtain ⟨hW1R, hW2R, hW3R⟩ := starImg_W_le_pCore hc D hRstar
  obtain ⟨hcard1, hcard2, hcard3⟩ := starImg_W_card D
  obtain ⟨helem, hcardR⟩ := starImg_elem_card hc D hRstar
  have hjoin : CFSG.pCore 3 (StarGroup 3 H) =
      starImg 3 H D.W₁ ⊔ starImg 3 H D.W₂ ⊔ starImg 3 H D.W₃ :=
    starImg_V_eq_sup_W hc D hRstar.symm
  have hmem1 : D.t₁ ∈ H := (D.t₁_mem hc.data).1
  have hmem2 : D.t₂ ∈ H := (D.t₂_mem hc.data).1
  have hmem3 : D.t₃ ∈ H := (D.t₃_mem hc.data).1
  let t1 : StarGroup 3 H :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨D.t₁, hmem1⟩
  let t2 : StarGroup 3 H :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨D.t₂, hmem2⟩
  let t3 : StarGroup 3 H :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨D.t₃, hmem3⟩
  have hcommR := elemAbelian_mul_comm helem
  have hinv1 := starImg_conjNormal_inv hc D hRstar hmem1 hW1H hW1DV D.cfg.inv₁
  have hinv2 := starImg_conjNormal_inv hc D hRstar hmem2 hW2H hW2DV D.cfg.inv₂
  have hinv3 := starImg_conjNormal_inv hc D hRstar hmem3 hW3H hW3DV D.cfg.inv₃
  have hfix12 := starImg_conjNormal_fix hc D hRstar hmem1 hW2H hW2DV
    (fun w hw => D.cfg.comm₁ w (Subgroup.mem_sup_left hw))
  have hfix13 := starImg_conjNormal_fix hc D hRstar hmem1 hW3H hW3DV
    (fun w hw => D.cfg.comm₁ w (Subgroup.mem_sup_right hw))
  have hfix21 := starImg_conjNormal_fix hc D hRstar hmem2 hW1H hW1DV
    (fun w hw => D.cfg.comm₂ w (Subgroup.mem_sup_left hw))
  have hfix23 := starImg_conjNormal_fix hc D hRstar hmem2 hW3H hW3DV
    (fun w hw => D.cfg.comm₂ w (Subgroup.mem_sup_right hw))
  have hfix31 := starImg_conjNormal_fix hc D hRstar hmem3 hW1H hW1DV
    (fun w hw => D.cfg.comm₃ w (Subgroup.mem_sup_left hw))
  have hfix32 := starImg_conjNormal_fix hc D hRstar hmem3 hW2H hW2DV
    (fun w hw => D.cfg.comm₃ w (Subgroup.mem_sup_right hw))
  have hcomm1 : ∀ x ∈ starImg 3 H D.W₂ ⊔ starImg 3 H D.W₃, t1 * x = x * t1 :=
    conj_comm_of_mem_sup (fun a ha b hb => hcommR a b (hW2R ha) (hW3R hb)) hfix12 hfix13
  have hcomm2 : ∀ x ∈ starImg 3 H D.W₁ ⊔ starImg 3 H D.W₃, t2 * x = x * t2 :=
    conj_comm_of_mem_sup (fun a ha b hb => hcommR a b (hW1R ha) (hW3R hb)) hfix21 hfix23
  have hcomm3 : ∀ x ∈ starImg 3 H D.W₁ ⊔ starImg 3 H D.W₂, t3 * x = x * t3 :=
    conj_comm_of_mem_sup (fun a ha b hb => hcommR a b (hW1R ha) (hW2R hb)) hfix31 hfix32
  exact ⟨hcard1, hcard2, hcard3, hjoin, helem, hcardR, hinv1, hinv2, hinv3,
    hcomm1, hcomm2, hcomm3⟩


private theorem relPPrimeCore_three_le_M
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃) :
    relPPrimeCore 3 H ≤ M := by
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := hc.ctx.exists_E_sq
  exact relPPrimeCore_le_of_gamma (Q := Q) hc.ctx.p_prime (hEQ.trans hc.ctx.Q_le_H) hE hEc hΓ

private theorem normalizer_W1_le_M
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    Subgroup.normalizer (D.W₁ : Set G) ≤ M :=
  normalizer_le_of_inverted D.cfg.card₁ (D.centralizer_le₁ hc) (D.t₁_mem hc.data).2
    D.cfg.inv₁

private theorem map_conj_W1_le_sup_of_starImg_eq
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {h : G} (hh : h ∈ H)
    (hstar : starImg 3 H (D.W₁.map (MulAut.conj h).toMonoidHom) = starImg 3 H D.W₁) :
    D.W₁.map (MulAut.conj h).toMonoidHom ≤ D.W₁ ⊔ relPPrimeCore 3 H := by
  have hW1H : D.W₁ ≤ H := D.le₁.trans (D.le_inf₁.trans inf_le_left)
  have hW1hH : D.W₁.map (MulAut.conj h).toMonoidHom ≤ H := by
    calc D.W₁.map (MulAut.conj h).toMonoidHom
        ≤ H.map (MulAut.conj h).toMonoidHom := Subgroup.map_mono hW1H
      _ = H := Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
  exact le_sup_relPPrimeCore_of_starImg_le Nat.prime_three hW1hH (le_of_eq hstar)

private theorem mem_M_of_map_conj_W1_le_sup
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {h : G} (hh : h ∈ H)
    (hle : D.W₁.map (MulAut.conj h).toMonoidHom ≤ D.W₁ ⊔ relPPrimeCore 3 H) :
    h ∈ M := by
  have hW1H : D.W₁ ≤ H := D.le₁.trans (D.le_inf₁.trans inf_le_left)
  have hO3 : ¬ 3 ∣ Nat.card (relPPrimeCore 3 H) :=
    hc.not_three_dvd_card_relPPrimeCore D
  have hOnorm : ((relPPrimeCore 3 H).subgroupOf H).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three H
  have hOH : relPPrimeCore 3 H ≤ H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le H
  have hHN : H ≤ Subgroup.normalizer (relPPrimeCore 3 H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mp hOnorm
  have hW1O : D.W₁ ≤ Subgroup.normalizer (relPPrimeCore 3 H : Set G) :=
    hW1H.trans hHN
  have hW1_3 : IsPGroup 3 D.W₁ := IsPGroup.of_card (n := 1) (by rw [D.cfg.card₁]; norm_num)
  have hsW : ∀ w ∈ D.W₁, h * w * h⁻¹ ∈ D.W₁ ⊔ relPPrimeCore 3 H := by
    intro w hw
    exact hle (Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hw)
  obtain ⟨o, hoO, hohN⟩ := exists_mul_mem_normalizer_of_not_three_dvd hO3 hW1_3 hW1O hsW
  have hN : Subgroup.normalizer (D.W₁ : Set G) ≤ M := normalizer_W1_le_M hc D
  have hOM : relPPrimeCore 3 H ≤ M := relPPrimeCore_three_le_M hc
  have hM : h ∈ M := by
    have h1 : o * h ∈ M := hN hohN
    have h2 : o⁻¹ ∈ M := M.inv_mem (hOM hoO)
    have heq : h = o⁻¹ * (o * h) := by group
    rw [heq]
    exact M.mul_mem h2 h1
  exact hM

private theorem stabilizer_le_starImg_M
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {y : StarGroup 3 H}
    (hy : (MulAut.conj y) • (starImg 3 H D.W₁) = starImg 3 H D.W₁) :
    y ∈ starImg 3 H M := by
  classical
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) 3
  let π : ↥H →* StarGroup 3 H := QuotientGroup.mk' O
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective O y
  have hmono : MulDistribMulAction.toMonoidHom (StarGroup 3 H) (MulAut.conj (π h)) =
      (MulAut.conj (π h)).toMonoidHom := by
    ext z
    rfl
  have hmap : (starImg 3 H D.W₁).map (MulAut.conj (π h)).toMonoidHom =
      starImg 3 H D.W₁ := by
    have hy' : (starImg 3 H D.W₁).map
        (MulDistribMulAction.toMonoidHom (StarGroup 3 H) (MulAut.conj (π h))) =
          starImg 3 H D.W₁ := hy
    rw [hmono] at hy'
    simpa [Subgroup.pointwise_smul_def] using hy' 
  have hstar : starImg 3 H (D.W₁.map (MulAut.conj (h : G)).toMonoidHom) =
      starImg 3 H D.W₁ := by
    rw [starImg_map_conj]
    exact hmap
  have hle := map_conj_W1_le_sup_of_starImg_eq hc D h.2 hstar
  have hM := mem_M_of_map_conj_W1_le_sup hc D h.2 hle
  exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hM)


private theorem le_of_starImg_le_of_le_V0
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hO : D.V ⊓ relPPrimeCore 3 H = ⊥)
    {A B : Subgroup G} (hA : A ≤ D.V) (hB : B ≤ D.V)
    (hAB : starImg 3 H A ≤ starImg 3 H B) : A ≤ B := by
  classical
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) 3
  let π : ↥H →* StarGroup 3 H := QuotientGroup.mk' O
  have hDVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  have hAH : A ≤ H := hA.trans hDVH
  intro x hx
  have hxπ_A : π ⟨x, hAH hx⟩ ∈ starImg 3 H A :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hAB hxπ_A)
  have hyB : (y : G) ∈ B := Subgroup.mem_subgroupOf.mp hy
  have hyV : (y : G) ∈ D.V := hB hyB
  have hker : π (y⁻¹ * ⟨x, hAH hx⟩) = 1 := by
    rw [map_mul, map_inv, hyx, inv_mul_cancel]
  have hmemO : y⁻¹ * ⟨x, hAH hx⟩ ∈ O := (QuotientGroup.eq_one_iff _).mp hker
  have hmemO' : (y : G)⁻¹ * x ∈ relPPrimeCore 3 H := by
    rw [nineTenGen_relPPrimeCore_eq_map Nat.prime_three H]
    exact Subgroup.mem_map_of_mem H.subtype hmemO
  have hmemV : (y : G)⁻¹ * x ∈ D.V :=
    D.V.mul_mem (D.V.inv_mem hyV) (hA hx)
  have hbot : (y : G)⁻¹ * x ∈ (⊥ : Subgroup G) := by
    rw [← hO]
    exact ⟨hmemV, hmemO'⟩
  have heq : (y : G) = x := by
    have h1 : (y : G)⁻¹ * x = 1 := Subgroup.mem_bot.mp hbot
    calc (y : G) = (y : G) * ((y : G)⁻¹ * x) := by rw [h1, mul_one]
      _ = x := by group
  rwa [← heq]

private theorem starImg_eq_of_le_V0
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hO : D.V ⊓ relPPrimeCore 3 H = ⊥)
    {A B : Subgroup G} (hA : A ≤ D.V) (hB : B ≤ D.V)
    (hAB : starImg 3 H A = starImg 3 H B) : A = B := by
  refine le_antisymm ?_ ?_
  · exact le_of_starImg_le_of_le_V0 hc D hO hA hB (le_of_eq hAB)
  · exact le_of_starImg_le_of_le_V0 hc D hO hB hA (le_of_eq hAB.symm)


private theorem starImg_W_pairwise_ne
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hV0O : D.V ⊓ relPPrimeCore 3 H = ⊥) :
    starImg 3 H D.W₁ ≠ starImg 3 H D.W₂ ∧
      starImg 3 H D.W₁ ≠ starImg 3 H D.W₃ ∧
      starImg 3 H D.W₂ ≠ starImg 3 H D.W₃ := by
  have hne : D.W₁ ≠ D.W₂ ∧ D.W₁ ≠ D.W₃ ∧ D.W₂ ≠ D.W₃ :=
    ⟨D.cfg.W₁_ne_W₂, D.cfg.W₁_ne_W₃, D.cfg.W₂_ne_W₃⟩
  have hW1V : D.W₁ ≤ D.V := by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  have hW2V : D.W₂ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  have hW3V : D.W₃ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right
  refine ⟨fun h => hne.1 (starImg_eq_of_le_V0 hc D hV0O hW1V hW2V h),
    fun h => hne.2.1 (starImg_eq_of_le_V0 hc D hV0O hW1V hW3V h),
    fun h => hne.2.2 (starImg_eq_of_le_V0 hc D hV0O hW2V hW3V h)⟩

private theorem map_smul_conjNormal {X : Type} [Group X] {P : Subgroup X} [hP : P.Normal]
    (y : X) (A : Subgroup ↥P) :
    ((MulAut.conjNormal (H := P) y) • A).map P.subtype =
      (A.map P.subtype).map (MulAut.conj y).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  change ((A.map (MulAut.conjNormal (H := P) y).toMonoidHom).map P.subtype) =
    (A.map P.subtype).map (MulAut.conj y).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private instance subgroupConjNormalAction {X : Type} [Group X] (P : Subgroup X) [hP : P.Normal] :
    MulAction X (Subgroup ↥P) :=
  MulAction.compHom (Subgroup ↥P) (MulAut.conjNormal (H := P))

private theorem map_smul_eq_map_conj {X : Type} [Group X] {P : Subgroup X} [hP : P.Normal]
    (y : X) (A : Subgroup ↥P) :
    (y • A).map P.subtype = (A.map P.subtype).map (MulAut.conj y).toMonoidHom := by
  rw [MulAction.compHom_smul_def]
  exact map_smul_conjNormal y A

private theorem card_smul_subgroup {X : Type} [Group X] {P : Subgroup X} [hP : P.Normal]
    (y : X) (A : Subgroup ↥P) : Nat.card ↥(y • A) = Nat.card ↥A := by
  rw [MulAction.compHom_smul_def, Subgroup.pointwise_smul_def]
  change Nat.card (A.map (MulAut.conjNormal (H := P) y).toMonoidHom) = Nat.card A
  exact Subgroup.card_map_of_injective (MulAut.conjNormal (H := P) y).injective

private theorem subgroupOf_map_subtype_self {X : Type} [Group X] {P : Subgroup X}
    (A : Subgroup ↥P) : (A.map P.subtype).subgroupOf P = A := by
  apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le A)]

private theorem ncard_modEq_ncard_fixedPoints_of_invariant {P X : Type*} [Group P]
    [MulAction P X] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) {O : Set X} (hOf : O.Finite)
    (hO : ∀ g : P, ∀ x ∈ O, g • x ∈ O) :
    O.ncard ≡ (O ∩ MulAction.fixedPoints P X).ncard [MOD p] := by
  let T : SubMulAction P X := ⟨O, fun {g x} hx => hO g x hx⟩
  haveI : Finite T := hOf.to_subtype
  have h := hP.card_modEq_card_fixedPoints T
  have e1 : Nat.card T = O.ncard := rfl
  have e2 : Nat.card (MulAction.fixedPoints P T) =
      (O ∩ MulAction.fixedPoints P X).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, fun g => congrArg Subtype.val (x.2 g)⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, fun g => Subtype.ext (x.2.2 g)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [e1, e2] at h
  exact h

private theorem exists_mem_starImg_M_smul_eq_of_map_conj
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    (S : SetupData hc D hn) {P : Subgroup (StarGroup 3 H)} [hP : P.Normal]
    (hW1P : starImg 3 H D.W₁ ≤ P) {W : Subgroup G} (hWP : starImg 3 H W ≤ P)
    {x : G} (hxV : x ∈ S.V)
    (hxW : D.W₁.map (MulAut.conj x).toMonoidHom = W) :
    ∃ y ∈ starImg 3 H M, y • (starImg 3 H D.W₁).subgroupOf P =
      (starImg 3 H W).subgroupOf P := by
  have hxH : x ∈ H := (S.hVHM hxV).1
  have hxM : x ∈ M := S.hVM hxV
  let y : StarGroup 3 H := QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨x, hxH⟩
  refine ⟨y, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxM), ?_⟩
  apply Subgroup.map_injective P.subtype_injective
  rw [map_smul_eq_map_conj, Subgroup.map_subgroupOf_eq_of_le hW1P,
    Subgroup.map_subgroupOf_eq_of_le hWP]
  have hstar := starImg_map_conj 3 H D.W₁ ⟨x, hxH⟩
  rw [hxW] at hstar
  exact hstar.symm

private theorem conjNormal_smul_subgroupOf_of_fixes {X : Type} [Group X] {P W : Subgroup X}
    [hP : P.Normal] (y : X) (hWP : W ≤ P) (hfix : ∀ w ∈ W, y * w * y⁻¹ = w) :
    (MulAut.conjNormal (H := P) y) • (W.subgroupOf P) = W.subgroupOf P := by
  apply Subgroup.map_injective P.subtype_injective
  rw [map_smul_conjNormal, Subgroup.map_subgroupOf_eq_of_le hWP]
  apply le_antisymm
  · rintro z ⟨w, hw, rfl⟩
    change MulAut.conj y w ∈ W
    rw [MulAut.conj_apply, hfix w hw]
    exact hw
  · intro z hz
    exact Subgroup.mem_map.mpr ⟨z, hz, by
      change MulAut.conj y z = z
      rw [MulAut.conj_apply, hfix z hz]⟩

private theorem conjNormal_smul_subgroupOf_of_inv {X : Type} [Group X] {P W : Subgroup X}
    [hP : P.Normal] (y : X) (hWP : W ≤ P) (hinv : ∀ w ∈ W, y * w * y⁻¹ = w⁻¹) :
    (MulAut.conjNormal (H := P) y) • (W.subgroupOf P) = W.subgroupOf P := by
  apply Subgroup.map_injective P.subtype_injective
  rw [map_smul_conjNormal, Subgroup.map_subgroupOf_eq_of_le hWP]
  apply le_antisymm
  · rintro z ⟨w, hw, rfl⟩
    change MulAut.conj y w ∈ W
    rw [MulAut.conj_apply, hinv w hw]
    exact W.inv_mem hw
  · intro z hz
    refine Subgroup.mem_map.mpr ⟨z⁻¹, W.inv_mem hz, ?_⟩
    change MulAut.conj y z⁻¹ = z
    rw [MulAut.conj_apply, hinv z⁻¹ (W.inv_mem hz), inv_inv]

private theorem three_le_ncard_orbit_starImg_M
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    (S : SetupData hc D hn) {P : Subgroup (StarGroup 3 H)} [hP : P.Normal]
    (hW1P : starImg 3 H D.W₁ ≤ P) (hW2P : starImg 3 H D.W₂ ≤ P)
    (hW3P : starImg 3 H D.W₃ ≤ P)
    (hne : starImg 3 H D.W₁ ≠ starImg 3 H D.W₂ ∧
      starImg 3 H D.W₁ ≠ starImg 3 H D.W₃ ∧
      starImg 3 H D.W₂ ≠ starImg 3 H D.W₃)
    (h₂ : ∃ x ∈ S.V, D.W₁.map (MulAut.conj x).toMonoidHom = D.W₂)
    (h₃ : ∃ x ∈ S.V, D.W₁.map (MulAut.conj x).toMonoidHom = D.W₃) :
    3 ≤ (MulAction.orbit (starImg 3 H M) ((starImg 3 H D.W₁).subgroupOf P)).ncard := by
  classical
  let ω1 : Subgroup ↥P := (starImg 3 H D.W₁).subgroupOf P
  let ω2 : Subgroup ↥P := (starImg 3 H D.W₂).subgroupOf P
  let ω3 : Subgroup ↥P := (starImg 3 H D.W₃).subgroupOf P
  have hmem2 : ∃ y ∈ starImg 3 H M, y • ω1 = ω2 := by
    obtain ⟨x, hxV, hxW⟩ := h₂
    exact exists_mem_starImg_M_smul_eq_of_map_conj hc D hn S hW1P hW2P hxV hxW
  have hmem3 : ∃ y ∈ starImg 3 H M, y • ω1 = ω3 := by
    obtain ⟨x, hxV, hxW⟩ := h₃
    exact exists_mem_starImg_M_smul_eq_of_map_conj hc D hn S hW1P hW3P hxV hxW
  have hsub : ({ω1, ω2, ω3} : Set (Subgroup ↥P)) ⊆
      MulAction.orbit (starImg 3 H M) ω1 := by
    intro A hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl | rfl
    · exact MulAction.mem_orbit_self ω1
    · obtain ⟨y, hy, hyω⟩ := hmem2
      exact ⟨⟨y, hy⟩, hyω⟩
    · obtain ⟨y, hy, hyω⟩ := hmem3
      exact ⟨⟨y, hy⟩, hyω⟩
  have h12 : ω1 ≠ ω2 := by
    intro h
    apply hne.1
    have hmap := congrArg (Subgroup.map P.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hW1P,
      Subgroup.map_subgroupOf_eq_of_le hW2P] at hmap
  have h13 : ω1 ≠ ω3 := by
    intro h
    apply hne.2.1
    have hmap := congrArg (Subgroup.map P.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hW1P,
      Subgroup.map_subgroupOf_eq_of_le hW3P] at hmap
  have h23 : ω2 ≠ ω3 := by
    intro h
    apply hne.2.2
    have hmap := congrArg (Subgroup.map P.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hW2P,
      Subgroup.map_subgroupOf_eq_of_le hW3P] at hmap
  have h3card : ({ω1, ω2, ω3} : Set (Subgroup ↥P)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [h12, h13]),
      Set.ncard_insert_of_notMem (by simp [h23]), Set.ncard_singleton]
  calc 3 = ({ω1, ω2, ω3} : Set (Subgroup ↥P)).ncard := h3card.symm
    _ ≤ (MulAction.orbit (starImg 3 H M) ω1).ncard := Set.ncard_le_ncard hsub

private theorem ncard_orbit_le_thirteen {X : Type} [Group X] [Finite X] {P : Subgroup X}
    [hP : P.Normal] (hPcard : Nat.card P = 27)
    {W : Subgroup X} (hWP : W ≤ P) (hWcard : Nat.card W = 3) :
    (MulAction.orbit X (W.subgroupOf P)).ncard ≤ 13 := by
  classical
  let ω := W.subgroupOf P
  let T : Set (Subgroup X) := {B | B ≤ P ∧ Nat.card B = 3}
  have hT : T.ncard ≤ 13 := by
    have h := CFSG.GroupTheory.ncard_subgroups_card_prime_mul_le (p := 3) Nat.prime_three P
    rw [hPcard] at h
    have h' : T.ncard * 2 ≤ 26 := by simpa [T] using h
    omega
  have hωcard : Nat.card ω = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWP).toEquiv, hWcard]
  have hcard : ∀ A ∈ MulAction.orbit X ω, Nat.card A = 3 := by
    rintro A ⟨y, rfl⟩
    rw [card_smul_subgroup, hωcard]
  have hmaps : ∀ A ∈ MulAction.orbit X ω, A.map P.subtype ∈ T := by
    intro A hA
    exact ⟨Subgroup.map_subtype_le A,
      Subgroup.card_map_of_injective P.subtype_injective ▸ hcard A hA⟩
  have hinj : Set.InjOn (fun A : Subgroup ↥P => A.map P.subtype) (MulAction.orbit X ω) := by
    intro A _ B _ hAB
    exact Subgroup.map_injective P.subtype_injective hAB
  calc (MulAction.orbit X ω).ncard ≤ T.ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj
    _ ≤ 13 := hT

private theorem mem_starImg_M_of_stabilizer
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {P : Subgroup (StarGroup 3 H)} [hP : P.Normal]
    (hW1P : starImg 3 H D.W₁ ≤ P) {y : StarGroup 3 H}
    (hy : y • (starImg 3 H D.W₁).subgroupOf P = (starImg 3 H D.W₁).subgroupOf P) :
    y ∈ starImg 3 H M := by
  apply stabilizer_le_starImg_M hc D
  have hmap := congrArg (Subgroup.map P.subtype) hy
  rw [map_smul_eq_map_conj] at hmap
  rw [Subgroup.map_subgroupOf_eq_of_le hW1P] at hmap
  change (starImg 3 H D.W₁).map (MulAut.conj y).toMonoidHom = starImg 3 H D.W₁
  exact hmap

private theorem not_three_dvd_index_starImg_M
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    (S : SetupData hc D hn) :
    ¬ 3 ∣ (starImg 3 H M).index := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S₀, hS₀⟩ := isSylowOf_starImg_of_isSylowOf S.hVsylH
  have hle : (S₀ : Subgroup (StarGroup 3 H)) ≤ starImg 3 H M := by
    rw [hS₀]
    exact Subgroup.map_mono (Subgroup.comap_mono S.hVM)
  have hdvd : (starImg 3 H M).index ∣ (S₀ : Subgroup (StarGroup 3 H)).index :=
    Subgroup.index_dvd_of_le hle
  exact fun h3 => S₀.not_dvd_index (h3.trans hdvd)

private theorem false_of_isSylowOf_le (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hp : p = 3) {V R : Subgroup G} (hV : CFSG.ABGLocalTools.IsSylowOf 3 V H)
    (hR : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H)) (hVR : V ≤ R) : False := by
  subst p
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := hc.ctx.exists_E_sq
  have hd : NineSettingGen G M 3 E H E 2 :=
    (hc.ctx.hypCGen hEQ hE hEc hΓ).toNineSettingGen
  have hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hc.ctx.p_not_mem_sigma
  have hU : NineNineOne M 3 := hc.hI G M E H E 3 hd hpσ
  have hstarV_le : starImg 3 H V ≤ CFSG.pCore 3 (StarGroup 3 H) := by
    rw [← hR]
    exact Subgroup.map_mono (Subgroup.comap_mono hVR)
  obtain ⟨S, hS⟩ := isSylowOf_starImg_of_isSylowOf hV
  have hpCore_le_S : CFSG.pCore 3 (StarGroup 3 H) ≤ S :=
    (CFSG.pCore_isPGroup (p := 3) (G := StarGroup 3 H)).le_sylow_of_normal S
  have hS_eq : (S : Subgroup (StarGroup 3 H)) = CFSG.pCore 3 (StarGroup 3 H) :=
    le_antisymm (hS ▸ hstarV_le) hpCore_le_S
  haveI hSnormal : (S : Subgroup (StarGroup 3 H)).Normal := by
    rw [hS_eq]
    exact CFSG.pCore_normal (p := 3) (G := StarGroup 3 H)
  haveI : Unique (Sylow 3 (StarGroup 3 H)) := Sylow.unique_of_normal S hSnormal
  have hE3 : IsPGroup 3 (starImg 3 H E) :=
    ((CFSG.Open.IsElemAbelian.isPGroup hE).comap_subtype (K := H)).map
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3))
  obtain ⟨SE, hSE⟩ := hE3.exists_le_sylow
  have hSE_eq : (SE : Subgroup (StarGroup 3 H)) = CFSG.pCore 3 (StarGroup 3 H) := by
    rw [show SE = S from Subsingleton.elim SE S, hS_eq]
  exact NineSettingGen.not_starImg_le_pCore hd hpσ hU (hSE.trans (le_of_eq hSE_eq))


private abbrev starP (H : Subgroup G) : Subgroup (StarGroup 3 H) :=
  CFSG.pCore 3 (StarGroup 3 H)

private noncomputable abbrev starW (H : Subgroup G) (W : Subgroup G) : Subgroup ↥(starP H) :=
  (starImg 3 H W).subgroupOf (starP H)

private noncomputable abbrev starT (H : Subgroup G) (t : G) (ht : t ∈ H) : StarGroup 3 H :=
  QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨t, ht⟩

private noncomputable abbrev starSigma (H : Subgroup G) (t : G) (ht : t ∈ H) : MulAut ↥(starP H) :=
  MulAut.conjNormal (H := starP H) (starT H t ht)

private theorem starE27Config_of_not_le
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    (S : SetupData hc D hn) (hle : ¬ S.V ≤ S.R) :
    starImg 3 H D.V = starP H ∧
      IsE27InvConfig (starP H) (starImg 3 H D.W₁) (starImg 3 H D.W₂)
        (starImg 3 H D.W₃) (starT H D.t₁ (D.t₁_mem hc.data).1)
        (starT H D.t₂ (D.t₂_mem hc.data).1) (starT H D.t₃ (D.t₃_mem hc.data).1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVR : S.V ⊓ S.R = D.V :=
    inf_eq_V0_of_not_le hc D hn S.hV3 S.hVM S.hV0V S.hV0R hle
  have hRstar_le : starP H ≤ starImg 3 H D.V :=
    pCore_le_starImg_V0_of_inf_le hc D S.hRsup S.hstarR (le_of_eq hVR)
  have hRstar : starImg 3 H D.V = starP H := le_antisymm S.hV0star hRstar_le
  exact ⟨hRstar, isE27InvConfig_star hc D hRstar⟩

private theorem starOmega_basic
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hE27 : IsE27InvConfig (starP H) (starImg 3 H D.W₁) (starImg 3 H D.W₂)
      (starImg 3 H D.W₃) (starT H D.t₁ (D.t₁_mem hc.data).1)
      (starT H D.t₂ (D.t₂_mem hc.data).1) (starT H D.t₃ (D.t₃_mem hc.data).1)) :
    starImg 3 H D.W₁ ≤ starP H ∧ starImg 3 H D.W₂ ≤ starP H ∧
      starImg 3 H D.W₃ ≤ starP H ∧ Nat.card (starW H D.W₁) = 3 := by
  have hW1P : starImg 3 H D.W₁ ≤ starP H := by
    rw [hE27.join]; exact le_sup_left.trans le_sup_left
  have hW2P : starImg 3 H D.W₂ ≤ starP H := by
    rw [hE27.join]; exact le_sup_right.trans le_sup_left
  have hW3P : starImg 3 H D.W₃ ≤ starP H := by
    rw [hE27.join]; exact le_sup_right
  have hcard : Nat.card (starW H D.W₁) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1P).toEquiv, hE27.card₁]
  exact ⟨hW1P, hW2P, hW3P, hcard⟩


private theorem sigma_inv_fix
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hRstar : starImg 3 H D.V = starP H)
    (hW1H : D.W₁ ≤ H) (hW2H : D.W₂ ≤ H) (hW3H : D.W₃ ≤ H)
    (hW1P : starImg 3 H D.W₁ ≤ starP H) (hW2P : starImg 3 H D.W₂ ≤ starP H)
    (hW3P : starImg 3 H D.W₃ ≤ starP H) :
    (∀ x ∈ starW H D.W₁, starSigma H D.t₁ (D.t₁_mem hc.data).1 x = x⁻¹) ∧
    (∀ x ∈ starW H D.W₂, starSigma H D.t₂ (D.t₂_mem hc.data).1 x = x⁻¹) ∧
    (∀ x ∈ starW H D.W₂, starSigma H D.t₁ (D.t₁_mem hc.data).1 x = x) ∧
    (∀ x ∈ starW H D.W₃, starSigma H D.t₁ (D.t₁_mem hc.data).1 x = x) ∧
    (∀ x ∈ starW H D.W₁, starSigma H D.t₂ (D.t₂_mem hc.data).1 x = x) ∧
    (∀ x ∈ starW H D.W₃, starSigma H D.t₂ (D.t₂_mem hc.data).1 x = x) := by
  obtain ⟨-, hW1DV, hW2DV, hW3DV⟩ := W_le_H_and_DV D
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := conjNormal_inv_of_inv (t := D.t₁) (D.t₁_mem hc.data).1 hW1H D.cfg.inv₁ x
      (Subgroup.mem_subgroupOf.mp hx)
    simpa [starSigma, starT, MulAut.conjNormal_apply] using h
  · intro x hx
    have h := conjNormal_inv_of_inv (t := D.t₂) (D.t₂_mem hc.data).1 hW2H D.cfg.inv₂ x
      (Subgroup.mem_subgroupOf.mp hx)
    simpa [starSigma, starT, MulAut.conjNormal_apply] using h
  · intro x hx
    have h := conjNormal_fix_of_comm (t := D.t₁) (D.t₁_mem hc.data).1 hW2H
      (fun w hw => D.cfg.comm₁ w (Subgroup.mem_sup_left hw)) x
      (Subgroup.mem_subgroupOf.mp hx)
    simpa [starSigma, starT, MulAut.conjNormal_apply] using h
  · intro x hx
    have h := conjNormal_fix_of_comm (t := D.t₁) (D.t₁_mem hc.data).1 hW3H
      (fun w hw => D.cfg.comm₁ w (Subgroup.mem_sup_right hw)) x
      (Subgroup.mem_subgroupOf.mp hx)
    simpa [starSigma, starT, MulAut.conjNormal_apply] using h
  · intro x hx
    have h := conjNormal_fix_of_comm (t := D.t₂) (D.t₂_mem hc.data).1 hW1H
      (fun w hw => D.cfg.comm₂ w (Subgroup.mem_sup_left hw)) x
      (Subgroup.mem_subgroupOf.mp hx)
    simpa [starSigma, starT, MulAut.conjNormal_apply] using h
  · intro x hx
    have h := conjNormal_fix_of_comm (t := D.t₂) (D.t₂_mem hc.data).1 hW3H
      (fun w hw => D.cfg.comm₂ w (Subgroup.mem_sup_right hw)) x
      (Subgroup.mem_subgroupOf.mp hx)
    simpa [starSigma, starT, MulAut.conjNormal_apply] using h

private theorem starOmega_join
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hE27 : IsE27InvConfig (starP H) (starImg 3 H D.W₁) (starImg 3 H D.W₂)
      (starImg 3 H D.W₃) (starT H D.t₁ (D.t₁_mem hc.data).1)
      (starT H D.t₂ (D.t₂_mem hc.data).1) (starT H D.t₃ (D.t₃_mem hc.data).1))
    (hW1P : starImg 3 H D.W₁ ≤ starP H) (hW2P : starImg 3 H D.W₂ ≤ starP H)
    (hW3P : starImg 3 H D.W₃ ≤ starP H) :
    starW H D.W₁ ⊔ starW H D.W₂ ⊔ starW H D.W₃ = ⊤ := by
  dsimp only [starW]
  apply Subgroup.map_injective (starP H).subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le hW1P, Subgroup.map_subgroupOf_eq_of_le hW2P,
    Subgroup.map_subgroupOf_eq_of_le hW3P]
  exact hE27.join.symm

private theorem sigma_sq
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hjoin : starW H D.W₁ ⊔ starW H D.W₂ ⊔ starW H D.W₃ = ⊤)
    (hcommP : ∀ a b : ↥(starP H), a * b = b * a)
    (hinv1 : ∀ x ∈ starW H D.W₁, starSigma H D.t₁ (D.t₁_mem hc.data).1 x = x⁻¹)
    (hinv2 : ∀ x ∈ starW H D.W₂, starSigma H D.t₂ (D.t₂_mem hc.data).1 x = x⁻¹)
    (hfix12 : ∀ x ∈ starW H D.W₂, starSigma H D.t₁ (D.t₁_mem hc.data).1 x = x)
    (hfix13 : ∀ x ∈ starW H D.W₃, starSigma H D.t₁ (D.t₁_mem hc.data).1 x = x)
    (hfix21 : ∀ x ∈ starW H D.W₁, starSigma H D.t₂ (D.t₂_mem hc.data).1 x = x)
    (hfix23 : ∀ x ∈ starW H D.W₃, starSigma H D.t₂ (D.t₂_mem hc.data).1 x = x) :
    starSigma H D.t₁ (D.t₁_mem hc.data).1 ^ 2 = 1 ∧
      starSigma H D.t₂ (D.t₂_mem hc.data).1 ^ 2 = 1 := by
  let σ1 : MulAut ↥(starP H) := starSigma H D.t₁ (D.t₁_mem hc.data).1
  let σ2 : MulAut ↥(starP H) := starSigma H D.t₂ (D.t₂_mem hc.data).1
  have hinv1' : ∀ x ∈ starW H D.W₁, σ1 x = x⁻¹ := fun x hx => by
    simpa [σ1] using hinv1 x hx
  have hinv2' : ∀ x ∈ starW H D.W₂, σ2 x = x⁻¹ := fun x hx => by
    simpa [σ2] using hinv2 x hx
  have hfix12' : ∀ x ∈ starW H D.W₂, σ1 x = x := fun x hx => by
    simpa [σ1] using hfix12 x hx
  have hfix13' : ∀ x ∈ starW H D.W₃, σ1 x = x := fun x hx => by
    simpa [σ1] using hfix13 x hx
  have hfix21' : ∀ x ∈ starW H D.W₁, σ2 x = x := fun x hx => by
    simpa [σ2] using hfix21 x hx
  have hfix23' : ∀ x ∈ starW H D.W₃, σ2 x = x := fun x hx => by
    simpa [σ2] using hfix23 x hx
  have h1sq1 : ∀ x ∈ starW H D.W₁, (σ1 ^ 2) x = x := by
    intro x hx
    rw [pow_two, MulAut.mul_apply, hinv1' x hx, map_inv, hinv1' x hx, inv_inv]
  have h1sq2 : ∀ x ∈ starW H D.W₂, (σ1 ^ 2) x = x := by
    intro x hx
    rw [pow_two, MulAut.mul_apply, hfix12' x hx, hfix12' x hx]
  have h1sq3 : ∀ x ∈ starW H D.W₃, (σ1 ^ 2) x = x := by
    intro x hx
    rw [pow_two, MulAut.mul_apply, hfix13' x hx, hfix13' x hx]
  have h2sq1 : ∀ x ∈ starW H D.W₁, (σ2 ^ 2) x = x := by
    intro x hx
    rw [pow_two, MulAut.mul_apply, hfix21' x hx, hfix21' x hx]
  have h2sq2 : ∀ x ∈ starW H D.W₂, (σ2 ^ 2) x = x := by
    intro x hx
    rw [pow_two, MulAut.mul_apply, hinv2' x hx, map_inv, hinv2' x hx, inv_inv]
  have h2sq3 : ∀ x ∈ starW H D.W₃, (σ2 ^ 2) x = x := by
    intro x hx
    rw [pow_two, MulAut.mul_apply, hfix23' x hx, hfix23' x hx]
  have hσ1_sq : σ1 ^ 2 = 1 := by
    refine CFSG.Fischer.eq_one_of_trivial_sup
      (A := starW H D.W₁ ⊔ starW H D.W₂) (B := starW H D.W₃) hjoin ?_ ?_
    · exact mulAut_fix_of_fixes_sup (fun a _ b _ => hcommP a b) h1sq1 h1sq2
    · exact h1sq3
  have hσ2_sq : σ2 ^ 2 = 1 := by
    refine CFSG.Fischer.eq_one_of_trivial_sup (A := starW H D.W₁)
      (B := starW H D.W₂ ⊔ starW H D.W₃) ?_ h2sq1 ?_
    · rw [← sup_assoc]; exact hjoin
    · exact mulAut_fix_of_fixes_sup (fun a _ b _ => hcommP a b) h2sq2 h2sq3
  exact ⟨by simpa [σ1] using hσ1_sq, by simpa [σ2] using hσ2_sq⟩

private theorem sigma_comm
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hjoin : starW H D.W₁ ⊔ starW H D.W₂ ⊔ starW H D.W₃ = ⊤)
    (hcommP : ∀ a b : ↥(starP H), a * b = b * a)
    (hinv1 : ∀ x ∈ starW H D.W₁, starSigma H D.t₁ (D.t₁_mem hc.data).1 x = x⁻¹)
    (hinv2 : ∀ x ∈ starW H D.W₂, starSigma H D.t₂ (D.t₂_mem hc.data).1 x = x⁻¹)
    (hfix12 : ∀ x ∈ starW H D.W₂, starSigma H D.t₁ (D.t₁_mem hc.data).1 x = x)
    (hfix13 : ∀ x ∈ starW H D.W₃, starSigma H D.t₁ (D.t₁_mem hc.data).1 x = x)
    (hfix21 : ∀ x ∈ starW H D.W₁, starSigma H D.t₂ (D.t₂_mem hc.data).1 x = x)
    (hfix23 : ∀ x ∈ starW H D.W₃, starSigma H D.t₂ (D.t₂_mem hc.data).1 x = x) :
    starSigma H D.t₁ (D.t₁_mem hc.data).1 *
        starSigma H D.t₂ (D.t₂_mem hc.data).1 =
      starSigma H D.t₂ (D.t₂_mem hc.data).1 *
        starSigma H D.t₁ (D.t₁_mem hc.data).1 := by
  let σ1 : MulAut ↥(starP H) := starSigma H D.t₁ (D.t₁_mem hc.data).1
  let σ2 : MulAut ↥(starP H) := starSigma H D.t₂ (D.t₂_mem hc.data).1
  have hinv1' : ∀ x ∈ starW H D.W₁, σ1 x = x⁻¹ := fun x hx => by
    simpa [σ1] using hinv1 x hx
  have hinv2' : ∀ x ∈ starW H D.W₂, σ2 x = x⁻¹ := fun x hx => by
    simpa [σ2] using hinv2 x hx
  have hfix12' : ∀ x ∈ starW H D.W₂, σ1 x = x := fun x hx => by
    simpa [σ1] using hfix12 x hx
  have hfix13' : ∀ x ∈ starW H D.W₃, σ1 x = x := fun x hx => by
    simpa [σ1] using hfix13 x hx
  have hfix21' : ∀ x ∈ starW H D.W₁, σ2 x = x := fun x hx => by
    simpa [σ2] using hfix21 x hx
  have hfix23' : ∀ x ∈ starW H D.W₃, σ2 x = x := fun x hx => by
    simpa [σ2] using hfix23 x hx
  have hcomm1 : ∀ x ∈ starW H D.W₁, (σ1 * σ2) x = (σ2 * σ1) x := by
    intro x hx
    rw [MulAut.mul_apply, MulAut.mul_apply, hfix21' x hx, hinv1' x hx, map_inv,
      hfix21' x hx]
  have hcomm2 : ∀ x ∈ starW H D.W₂, (σ1 * σ2) x = (σ2 * σ1) x := by
    intro x hx
    rw [MulAut.mul_apply, MulAut.mul_apply, hinv2' x hx, map_inv, hfix12' x hx,
      hinv2' x hx]
  have hcomm3 : ∀ x ∈ starW H D.W₃, (σ1 * σ2) x = (σ2 * σ1) x := by
    intro x hx
    rw [MulAut.mul_apply, MulAut.mul_apply, hfix23' x hx, hfix13' x hx, hfix23' x hx]
  have hσcomm : σ1 * σ2 = σ2 * σ1 := by
    ext x
    simpa using mulAut_eq_of_agree_sup (A := starW H D.W₁) (B := starW H D.W₂)
      (C := starW H D.W₃) (fun a _ b _ => hcommP a b) (fun a _ b _ => hcommP a b)
      (fun a _ b _ => hcommP a b) (σ1 * σ2) (σ2 * σ1) hcomm1 hcomm2 hcomm3
      (by rw [hjoin]; exact Subgroup.mem_top x)
  simpa [σ1, σ2] using hσcomm

private theorem sigma_sq_comm
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hjoin : starW H D.W₁ ⊔ starW H D.W₂ ⊔ starW H D.W₃ = ⊤)
    (hcommP : ∀ a b : ↥(starP H), a * b = b * a)
    (hinv1 : ∀ x ∈ starW H D.W₁, starSigma H D.t₁ (D.t₁_mem hc.data).1 x = x⁻¹)
    (hinv2 : ∀ x ∈ starW H D.W₂, starSigma H D.t₂ (D.t₂_mem hc.data).1 x = x⁻¹)
    (hfix12 : ∀ x ∈ starW H D.W₂, starSigma H D.t₁ (D.t₁_mem hc.data).1 x = x)
    (hfix13 : ∀ x ∈ starW H D.W₃, starSigma H D.t₁ (D.t₁_mem hc.data).1 x = x)
    (hfix21 : ∀ x ∈ starW H D.W₁, starSigma H D.t₂ (D.t₂_mem hc.data).1 x = x)
    (hfix23 : ∀ x ∈ starW H D.W₃, starSigma H D.t₂ (D.t₂_mem hc.data).1 x = x) :
    starSigma H D.t₁ (D.t₁_mem hc.data).1 ^ 2 = 1 ∧
      starSigma H D.t₂ (D.t₂_mem hc.data).1 ^ 2 = 1 ∧
      starSigma H D.t₁ (D.t₁_mem hc.data).1 *
          starSigma H D.t₂ (D.t₂_mem hc.data).1 =
        starSigma H D.t₂ (D.t₂_mem hc.data).1 *
          starSigma H D.t₁ (D.t₁_mem hc.data).1 := by
  obtain ⟨h1, h2⟩ := sigma_sq hc D hjoin hcommP hinv1 hinv2 hfix12 hfix13 hfix21 hfix23
  exact ⟨h1, h2, sigma_comm hc D hjoin hcommP hinv1 hinv2 hfix12 hfix13 hfix21 hfix23⟩


private theorem closure_pair_le_stabilizer {X α : Type} [Group X] [MulAction X α]
    {a b : X} {x : α} (ha : a • x = x) (hb : b • x = x) :
    Subgroup.closure ({a, b} : Set X) ≤ MulAction.stabilizer X x := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact MulAction.mem_stabilizer_iff.mpr ha
  · exact MulAction.mem_stabilizer_iff.mpr hb

private theorem mem_fixedPoints_of_le_stabilizer {X α : Type} [Group X] [MulAction X α]
    {E : Subgroup X} {x : α} (h : E ≤ MulAction.stabilizer X x) :
    x ∈ MulAction.fixedPoints E α := by
  rw [MulAction.mem_fixedPoints]
  intro e
  exact (Subgroup.mk_smul (e : X) e.2 x).trans (MulAction.mem_stabilizer_iff.mp (h e.2))

private theorem sigma_smul
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hE27 : IsE27InvConfig (starP H) (starImg 3 H D.W₁) (starImg 3 H D.W₂)
      (starImg 3 H D.W₃) (starT H D.t₁ (D.t₁_mem hc.data).1)
      (starT H D.t₂ (D.t₂_mem hc.data).1) (starT H D.t₃ (D.t₃_mem hc.data).1))
    (hW1P : starImg 3 H D.W₁ ≤ starP H) (hW2P : starImg 3 H D.W₂ ≤ starP H)
    (hW3P : starImg 3 H D.W₃ ≤ starP H) :
    starSigma H D.t₁ (D.t₁_mem hc.data).1 • starW H D.W₁ = starW H D.W₁ ∧
    starSigma H D.t₁ (D.t₁_mem hc.data).1 • starW H D.W₂ = starW H D.W₂ ∧
    starSigma H D.t₁ (D.t₁_mem hc.data).1 • starW H D.W₃ = starW H D.W₃ ∧
    starSigma H D.t₂ (D.t₂_mem hc.data).1 • starW H D.W₁ = starW H D.W₁ ∧
    starSigma H D.t₂ (D.t₂_mem hc.data).1 • starW H D.W₂ = starW H D.W₂ ∧
    starSigma H D.t₂ (D.t₂_mem hc.data).1 • starW H D.W₃ = starW H D.W₃ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact conjNormal_smul_subgroupOf_of_inv (P := starP H) (W := starImg 3 H D.W₁)
      (starT H D.t₁ (D.t₁_mem hc.data).1) hW1P hE27.inv₁
  · refine conjNormal_smul_subgroupOf_of_fixes (P := starP H) (W := starImg 3 H D.W₂)
      (starT H D.t₁ (D.t₁_mem hc.data).1) hW2P ?_
    intro w hw
    have h := hE27.comm₁ w (Subgroup.mem_sup_left hw)
    calc starT H D.t₁ (D.t₁_mem hc.data).1 * w *
          (starT H D.t₁ (D.t₁_mem hc.data).1)⁻¹ =
        (w * starT H D.t₁ (D.t₁_mem hc.data).1) *
          (starT H D.t₁ (D.t₁_mem hc.data).1)⁻¹ := by rw [h]
      _ = w := by group
  · refine conjNormal_smul_subgroupOf_of_fixes (P := starP H) (W := starImg 3 H D.W₃)
      (starT H D.t₁ (D.t₁_mem hc.data).1) hW3P ?_
    intro w hw
    have h := hE27.comm₁ w (Subgroup.mem_sup_right hw)
    calc starT H D.t₁ (D.t₁_mem hc.data).1 * w *
          (starT H D.t₁ (D.t₁_mem hc.data).1)⁻¹ =
        (w * starT H D.t₁ (D.t₁_mem hc.data).1) *
          (starT H D.t₁ (D.t₁_mem hc.data).1)⁻¹ := by rw [h]
      _ = w := by group
  · refine conjNormal_smul_subgroupOf_of_fixes (P := starP H) (W := starImg 3 H D.W₁)
      (starT H D.t₂ (D.t₂_mem hc.data).1) hW1P ?_
    intro w hw
    have h := hE27.comm₂ w (Subgroup.mem_sup_left hw)
    calc starT H D.t₂ (D.t₂_mem hc.data).1 * w *
          (starT H D.t₂ (D.t₂_mem hc.data).1)⁻¹ =
        (w * starT H D.t₂ (D.t₂_mem hc.data).1) *
          (starT H D.t₂ (D.t₂_mem hc.data).1)⁻¹ := by rw [h]
      _ = w := by group
  · exact conjNormal_smul_subgroupOf_of_inv (P := starP H) (W := starImg 3 H D.W₂)
      (starT H D.t₂ (D.t₂_mem hc.data).1) hW2P hE27.inv₂
  · refine conjNormal_smul_subgroupOf_of_fixes (P := starP H) (W := starImg 3 H D.W₃)
      (starT H D.t₂ (D.t₂_mem hc.data).1) hW3P ?_
    intro w hw
    have h := hE27.comm₂ w (Subgroup.mem_sup_right hw)
    calc starT H D.t₂ (D.t₂_mem hc.data).1 * w *
          (starT H D.t₂ (D.t₂_mem hc.data).1)⁻¹ =
        (w * starT H D.t₂ (D.t₂_mem hc.data).1) *
          (starT H D.t₂ (D.t₂_mem hc.data).1)⁻¹ := by rw [h]
      _ = w := by group

private theorem sigma_closure_isPGroup
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hσ1_sq : starSigma H D.t₁ (D.t₁_mem hc.data).1 ^ 2 = 1)
    (hσ2_sq : starSigma H D.t₂ (D.t₂_mem hc.data).1 ^ 2 = 1)
    (hσcomm : starSigma H D.t₁ (D.t₁_mem hc.data).1 *
        starSigma H D.t₂ (D.t₂_mem hc.data).1 =
      starSigma H D.t₂ (D.t₂_mem hc.data).1 *
        starSigma H D.t₁ (D.t₁_mem hc.data).1) :
    IsPGroup 2 (Subgroup.closure
      ({starSigma H D.t₁ (D.t₁_mem hc.data).1,
        starSigma H D.t₂ (D.t₂_mem hc.data).1} : Set (MulAut ↥(starP H)))) := by
  let σ1 : MulAut ↥(starP H) := starSigma H D.t₁ (D.t₁_mem hc.data).1
  let σ2 : MulAut ↥(starP H) := starSigma H D.t₂ (D.t₂_mem hc.data).1
  have h1 : σ1 ^ 2 = 1 := by simpa [σ1] using hσ1_sq
  have h2 : σ2 ^ 2 = 1 := by simpa [σ2] using hσ2_sq
  have hc12 : σ1 * σ2 = σ2 * σ1 := by simpa [σ1, σ2] using hσcomm
  have hsq : (σ1 * σ2) ^ 2 = 1 := by
    rw [pow_two]
    calc σ1 * σ2 * (σ1 * σ2) = σ1 * (σ2 * σ1) * σ2 := by group
      _ = σ1 * (σ1 * σ2) * σ2 := by rw [hc12]
      _ = σ1 * σ1 * (σ2 * σ2) := by group
      _ = 1 := by rw [← pow_two, ← pow_two, h1, h2, one_mul]
  simpa [σ1, σ2] using
    (CFSG.Timmesfeld.isPGroup_two_closure_pair (d := σ1) (e := σ2)
      (by simpa [pow_two] using h1) (by simpa [pow_two] using h2) (k := 1) (by simpa using hsq))

private theorem orbit_invariant_of_le_range
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup (MulAut ↥(starP H))}
    (hE_le_range : E ≤ (MulAut.conjNormal (H := starP H)).range) :
    ∀ e : E, ∀ A ∈ MulAction.orbit (StarGroup 3 H) (starW H D.W₁),
      e • A ∈ MulAction.orbit (StarGroup 3 H) (starW H D.W₁) := by
  intro e A hA
  obtain ⟨y, hy⟩ := hE_le_range e.2
  have hsm : e • A = y • A := by
    rw [Subgroup.mk_smul, ← hy]
    rfl
  rw [hsm]
  obtain ⟨z, rfl⟩ := hA
  exact ⟨y * z, mul_smul y z (starW H D.W₁)⟩

private theorem sigma_twoGroup_fixed
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hσ1_sq : starSigma H D.t₁ (D.t₁_mem hc.data).1 ^ 2 = 1)
    (hσ2_sq : starSigma H D.t₂ (D.t₂_mem hc.data).1 ^ 2 = 1)
    (hσcomm : starSigma H D.t₁ (D.t₁_mem hc.data).1 *
        starSigma H D.t₂ (D.t₂_mem hc.data).1 =
      starSigma H D.t₂ (D.t₂_mem hc.data).1 *
        starSigma H D.t₁ (D.t₁_mem hc.data).1)
    (hσ1_inv_ω1 : starSigma H D.t₁ (D.t₁_mem hc.data).1 • starW H D.W₁ =
      starW H D.W₁)
    (hσ1_fix_ω2 : starSigma H D.t₁ (D.t₁_mem hc.data).1 • starW H D.W₂ =
      starW H D.W₂)
    (hσ1_fix_ω3 : starSigma H D.t₁ (D.t₁_mem hc.data).1 • starW H D.W₃ =
      starW H D.W₃)
    (hσ2_fix_ω1 : starSigma H D.t₂ (D.t₂_mem hc.data).1 • starW H D.W₁ =
      starW H D.W₁)
    (hσ2_inv_ω2 : starSigma H D.t₂ (D.t₂_mem hc.data).1 • starW H D.W₂ =
      starW H D.W₂)
    (hσ2_fix_ω3 : starSigma H D.t₂ (D.t₂_mem hc.data).1 • starW H D.W₃ =
      starW H D.W₃) :
    ∃ E : Subgroup (MulAut ↥(starP H)),
      IsPGroup 2 E ∧ E ≤ (MulAut.conjNormal (H := starP H)).range ∧
      starSigma H D.t₁ (D.t₁_mem hc.data).1 ∈ E ∧
      starSigma H D.t₂ (D.t₂_mem hc.data).1 ∈ E ∧
      (∀ e : E, ∀ A ∈ MulAction.orbit (StarGroup 3 H) (starW H D.W₁),
        e • A ∈ MulAction.orbit (StarGroup 3 H) (starW H D.W₁)) ∧
      starW H D.W₁ ∈ MulAction.fixedPoints E (Subgroup ↥(starP H)) ∧
      starW H D.W₂ ∈ MulAction.fixedPoints E (Subgroup ↥(starP H)) ∧
      starW H D.W₃ ∈ MulAction.fixedPoints E (Subgroup ↥(starP H)) := by
  let σ1 : MulAut ↥(starP H) := starSigma H D.t₁ (D.t₁_mem hc.data).1
  let σ2 : MulAut ↥(starP H) := starSigma H D.t₂ (D.t₂_mem hc.data).1
  let E : Subgroup (MulAut ↥(starP H)) := Subgroup.closure ({σ1, σ2} : Set _)
  have hE2 : IsPGroup 2 E := sigma_closure_isPGroup hc D hσ1_sq hσ2_sq hσcomm
  have hE_le_range : E ≤ (MulAut.conjNormal (H := starP H)).range := by
    rw [Subgroup.closure_le]
    intro σ hσ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl
    · exact ⟨starT H D.t₁ (D.t₁_mem hc.data).1, rfl⟩
    · exact ⟨starT H D.t₂ (D.t₂_mem hc.data).1, rfl⟩
  have hO := orbit_invariant_of_le_range D hE_le_range
  have hstab1 : E ≤ MulAction.stabilizer (MulAut ↥(starP H)) (starW H D.W₁) := by
    refine closure_pair_le_stabilizer (a := σ1) (b := σ2) ?_ ?_
    · simpa [σ1] using hσ1_inv_ω1
    · simpa [σ2] using hσ2_fix_ω1
  have hstab2 : E ≤ MulAction.stabilizer (MulAut ↥(starP H)) (starW H D.W₂) := by
    refine closure_pair_le_stabilizer (a := σ1) (b := σ2) ?_ ?_
    · simpa [σ1] using hσ1_fix_ω2
    · simpa [σ2] using hσ2_inv_ω2
  have hstab3 : E ≤ MulAction.stabilizer (MulAut ↥(starP H)) (starW H D.W₃) := by
    refine closure_pair_le_stabilizer (a := σ1) (b := σ2) ?_ ?_
    · simpa [σ1] using hσ1_fix_ω3
    · simpa [σ2] using hσ2_fix_ω3
  refine ⟨E, hE2, hE_le_range, ?_, ?_, hO, mem_fixedPoints_of_le_stabilizer hstab1,
    mem_fixedPoints_of_le_stabilizer hstab2, mem_fixedPoints_of_le_stabilizer hstab3⟩
  · refine Subgroup.subset_closure ?_
    show starSigma H D.t₁ (D.t₁_mem hc.data).1 ∈
      ({σ1, σ2} : Set (MulAut ↥(starP H)))
    exact Set.mem_insert _ _
  · refine Subgroup.subset_closure ?_
    show starSigma H D.t₂ (D.t₂_mem hc.data).1 ∈
      ({σ1, σ2} : Set (MulAut ↥(starP H)))
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

private theorem map_conj_invariant_of_fixed
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup (MulAut ↥(starP H))}
    (hσ1E : starSigma H D.t₁ (D.t₁_mem hc.data).1 ∈ E)
    (hσ2E : starSigma H D.t₂ (D.t₂_mem hc.data).1 ∈ E)
    {A : Subgroup ↥(starP H)} (hfix : A ∈ MulAction.fixedPoints E (Subgroup ↥(starP H))) :
    (∀ x ∈ A.map (starP H).subtype, starT H D.t₁ (D.t₁_mem hc.data).1 * x *
        (starT H D.t₁ (D.t₁_mem hc.data).1)⁻¹ ∈ A.map (starP H).subtype) ∧
      (∀ x ∈ A.map (starP H).subtype, starT H D.t₂ (D.t₂_mem hc.data).1 * x *
        (starT H D.t₂ (D.t₂_mem hc.data).1)⁻¹ ∈ A.map (starP H).subtype) := by
  rw [MulAction.mem_fixedPoints] at hfix
  have hA1 : starSigma H D.t₁ (D.t₁_mem hc.data).1 • A = A := hfix ⟨_, hσ1E⟩
  have hA2 : starSigma H D.t₂ (D.t₂_mem hc.data).1 • A = A := hfix ⟨_, hσ2E⟩
  have hmap1 : (A.map (starP H).subtype).map
      (MulAut.conj (starT H D.t₁ (D.t₁_mem hc.data).1)).toMonoidHom =
      A.map (starP H).subtype := by
    have h := congrArg (Subgroup.map (starP H).subtype) hA1
    rwa [map_smul_conjNormal] at h
  have hmap2 : (A.map (starP H).subtype).map
      (MulAut.conj (starT H D.t₂ (D.t₂_mem hc.data).1)).toMonoidHom =
      A.map (starP H).subtype := by
    have h := congrArg (Subgroup.map (starP H).subtype) hA2
    rwa [map_smul_conjNormal] at h
  have hD1 : ∀ x ∈ A.map (starP H).subtype,
      starT H D.t₁ (D.t₁_mem hc.data).1 * x *
        (starT H D.t₁ (D.t₁_mem hc.data).1)⁻¹ ∈ A.map (starP H).subtype := by
    intro x hx
    have hx' : MulAut.conj (starT H D.t₁ (D.t₁_mem hc.data).1) x ∈
        (A.map (starP H).subtype).map
          (MulAut.conj (starT H D.t₁ (D.t₁_mem hc.data).1)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [hmap1] at hx'
    simpa [MulAut.conj_apply] using hx'
  have hD2 : ∀ x ∈ A.map (starP H).subtype,
      starT H D.t₂ (D.t₂_mem hc.data).1 * x *
        (starT H D.t₂ (D.t₂_mem hc.data).1)⁻¹ ∈ A.map (starP H).subtype := by
    intro x hx
    have hx' : MulAut.conj (starT H D.t₂ (D.t₂_mem hc.data).1) x ∈
        (A.map (starP H).subtype).map
          (MulAut.conj (starT H D.t₂ (D.t₂_mem hc.data).1)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [hmap2] at hx'
    simpa [MulAut.conj_apply] using hx'
  exact ⟨hD1, hD2⟩

private theorem mem_three_of_fixed
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hE27 : IsE27InvConfig (starP H) (starImg 3 H D.W₁) (starImg 3 H D.W₂)
      (starImg 3 H D.W₃) (starT H D.t₁ (D.t₁_mem hc.data).1)
      (starT H D.t₂ (D.t₂_mem hc.data).1) (starT H D.t₃ (D.t₃_mem hc.data).1))
    {E : Subgroup (MulAut ↥(starP H))}
    (hσ1E : starSigma H D.t₁ (D.t₁_mem hc.data).1 ∈ E)
    (hσ2E : starSigma H D.t₂ (D.t₂_mem hc.data).1 ∈ E)
    (hcardω1 : Nat.card (starW H D.W₁) = 3) {A : Subgroup ↥(starP H)}
    (hA : A ∈ MulAction.orbit (StarGroup 3 H) (starW H D.W₁))
    (hfix : A ∈ MulAction.fixedPoints E (Subgroup ↥(starP H))) :
    A = starW H D.W₁ ∨ A = starW H D.W₂ ∨ A = starW H D.W₃ := by
  classical
  obtain ⟨hD1, hD2⟩ := map_conj_invariant_of_fixed hc D hσ1E hσ2E hfix
  obtain ⟨y, rfl⟩ := hA
  have hcardA : Nat.card ↥(y • starW H D.W₁) = 3 := by
    rw [card_smul_subgroup, hcardω1]
  have hDcard : Nat.card ↥((y • starW H D.W₁).map (starP H).subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (starP H).subtype_injective, hcardA]
  rcases IsE27InvConfig.eq_W_of_invariant_two (D := (y • starW H D.W₁).map (starP H).subtype)
    hE27 (Subgroup.map_subtype_le _) hDcard hD1 hD2 with h | h | h
  · left
    calc y • starW H D.W₁ =
          ((y • starW H D.W₁).map (starP H).subtype).subgroupOf (starP H) :=
          (subgroupOf_map_subtype_self (y • starW H D.W₁)).symm
      _ = (starImg 3 H D.W₁).subgroupOf (starP H) := by rw [h]
      _ = starW H D.W₁ := rfl
  · right; left
    calc y • starW H D.W₁ =
          ((y • starW H D.W₁).map (starP H).subtype).subgroupOf (starP H) :=
          (subgroupOf_map_subtype_self (y • starW H D.W₁)).symm
      _ = (starImg 3 H D.W₂).subgroupOf (starP H) := by rw [h]
      _ = starW H D.W₂ := rfl
  · right; right
    calc y • starW H D.W₁ =
          ((y • starW H D.W₁).map (starP H).subtype).subgroupOf (starP H) :=
          (subgroupOf_map_subtype_self (y • starW H D.W₁)).symm
      _ = (starImg 3 H D.W₃).subgroupOf (starP H) := by rw [h]
      _ = starW H D.W₃ := rfl

private theorem fixedPoints_orbit_eq_three
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hE27 : IsE27InvConfig (starP H) (starImg 3 H D.W₁) (starImg 3 H D.W₂)
      (starImg 3 H D.W₃) (starT H D.t₁ (D.t₁_mem hc.data).1)
      (starT H D.t₂ (D.t₂_mem hc.data).1) (starT H D.t₃ (D.t₃_mem hc.data).1))
    {E : Subgroup (MulAut ↥(starP H))}
    (hσ1E : starSigma H D.t₁ (D.t₁_mem hc.data).1 ∈ E)
    (hσ2E : starSigma H D.t₂ (D.t₂_mem hc.data).1 ∈ E)
    (hcardω1 : Nat.card (starW H D.W₁) = 3)
    (hmemω2 : starW H D.W₂ ∈ MulAction.orbit (StarGroup 3 H) (starW H D.W₁))
    (hmemω3 : starW H D.W₃ ∈ MulAction.orbit (StarGroup 3 H) (starW H D.W₁))
    (hfixω1 : starW H D.W₁ ∈ MulAction.fixedPoints E (Subgroup ↥(starP H)))
    (hfixω2 : starW H D.W₂ ∈ MulAction.fixedPoints E (Subgroup ↥(starP H)))
    (hfixω3 : starW H D.W₃ ∈ MulAction.fixedPoints E (Subgroup ↥(starP H))) :
    MulAction.orbit (StarGroup 3 H) (starW H D.W₁) ∩
        MulAction.fixedPoints E (Subgroup ↥(starP H)) =
      ({starW H D.W₁, starW H D.W₂, starW H D.W₃} :
        Set (Subgroup ↥(starP H))) := by
  ext A
  constructor
  · rintro ⟨hA, hfix⟩
    exact mem_three_of_fixed hc D hE27 hσ1E hσ2E hcardω1 hA hfix
  · intro hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl | rfl
    · exact ⟨MulAction.mem_orbit_self _, hfixω1⟩
    · exact ⟨hmemω2, hfixω2⟩
    · exact ⟨hmemω3, hfixω3⟩

private theorem orbit_ncard_modEq_three
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup (MulAut ↥(starP H))} (hE2 : IsPGroup 2 E)
    (hO : ∀ e : E, ∀ A ∈ MulAction.orbit (StarGroup 3 H) (starW H D.W₁),
      e • A ∈ MulAction.orbit (StarGroup 3 H) (starW H D.W₁))
    (hfixset : MulAction.orbit (StarGroup 3 H) (starW H D.W₁) ∩
        MulAction.fixedPoints E (Subgroup ↥(starP H)) =
      ({starW H D.W₁, starW H D.W₂, starW H D.W₃} :
        Set (Subgroup ↥(starP H))))
    (h3card : ({starW H D.W₁, starW H D.W₂, starW H D.W₃} :
        Set (Subgroup ↥(starP H))).ncard = 3) :
    (MulAction.orbit (StarGroup 3 H) (starW H D.W₁)).ncard ≡ 3 [MOD 2] := by
  have hpar := ncard_modEq_ncard_fixedPoints_of_invariant (P := E) hE2
    (O := MulAction.orbit (StarGroup 3 H) (starW H D.W₁)) (Set.toFinite _) hO
  rw [hfixset, h3card] at hpar
  exact hpar

private theorem index_eq_one_of_orbit_count {k m n : ℕ} (hcount : k * m = n)
    (hm3 : 3 ≤ m) (hn13 : n ≤ 13) (hnot3 : ¬ 3 ∣ k) (hoddn : Odd n) : k = 1 := by
  have hoddk : Odd k := Nat.Odd.of_mul_left (hcount ▸ hoddn)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, zero_mul] at hcount
      omega
    · exact hpos
  have hkle4 : k ≤ 4 := by
    have h3k : 3 * k ≤ n := by
      calc 3 * k = k * 3 := Nat.mul_comm _ _
        _ ≤ k * m := Nat.mul_le_mul_left _ hm3
        _ = n := hcount
    omega
  interval_cases k
  · rfl
  · exact absurd hoddk (by norm_num)
  · exact absurd hnot3 (by norm_num)
  · exact absurd hoddk (by norm_num)

private theorem le_of_starImg_M_eq_top
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hKtop : starImg 3 H M = ⊤) : H ≤ M := by
  intro h hh
  have hmem : (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨h, hh⟩) ∈
      starImg 3 H M := by
    rw [hKtop]
    exact Subgroup.mem_top _
  obtain ⟨m, hm, hπm⟩ := Subgroup.mem_map.mp hmem
  have hmM : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
  have hker : QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) (m⁻¹ * ⟨h, hh⟩) = 1 := by
    rw [map_mul, map_inv, hπm, inv_mul_cancel]
  have hmemO : m⁻¹ * ⟨h, hh⟩ ∈ primeComplementCore (G := ↥H) 3 :=
    (QuotientGroup.eq_one_iff _).mp hker
  have hmemP : (m : G)⁻¹ * h ∈ relPPrimeCore 3 H := by
    rw [nineTenGen_relPPrimeCore_eq_map Nat.prime_three H]
    exact Subgroup.mem_map_of_mem H.subtype hmemO
  have hmemM : (m : G)⁻¹ * h ∈ M := relPPrimeCore_three_le_M hc hmemP
  have hprod : (m : G) * ((m : G)⁻¹ * h) ∈ M := M.mul_mem hmM hmemM
  simpa [mul_assoc] using hprod

private theorem orbit_members_of_conj
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    (S : SetupData hc D hn)
    (hW1P : starImg 3 H D.W₁ ≤ starP H) (hW2P : starImg 3 H D.W₂ ≤ starP H)
    (hW3P : starImg 3 H D.W₃ ≤ starP H)
    (h₂ : ∃ x ∈ S.V, D.W₁.map (MulAut.conj x).toMonoidHom = D.W₂)
    (h₃ : ∃ x ∈ S.V, D.W₁.map (MulAut.conj x).toMonoidHom = D.W₃) :
    starW H D.W₂ ∈ MulAction.orbit (StarGroup 3 H) (starW H D.W₁) ∧
      starW H D.W₃ ∈ MulAction.orbit (StarGroup 3 H) (starW H D.W₁) := by
  constructor
  · obtain ⟨x, hxV, hxW⟩ := h₂
    obtain ⟨y, -, hy⟩ :=
      exists_mem_starImg_M_smul_eq_of_map_conj hc D hn S hW1P hW2P hxV hxW
    exact ⟨y, hy⟩
  · obtain ⟨x, hxV, hxW⟩ := h₃
    obtain ⟨y, -, hy⟩ :=
      exists_mem_starImg_M_smul_eq_of_map_conj hc D hn S hW1P hW3P hxV hxW
    exact ⟨y, hy⟩

private theorem orbit_bounds
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    (S : SetupData hc D hn)
    (hE27 : IsE27InvConfig (starP H) (starImg 3 H D.W₁) (starImg 3 H D.W₂)
      (starImg 3 H D.W₃) (starT H D.t₁ (D.t₁_mem hc.data).1)
      (starT H D.t₂ (D.t₂_mem hc.data).1) (starT H D.t₃ (D.t₃_mem hc.data).1))
    (hWne : starImg 3 H D.W₁ ≠ starImg 3 H D.W₂ ∧
      starImg 3 H D.W₁ ≠ starImg 3 H D.W₃ ∧
      starImg 3 H D.W₂ ≠ starImg 3 H D.W₃)
    (hW1P : starImg 3 H D.W₁ ≤ starP H) (hW2P : starImg 3 H D.W₂ ≤ starP H)
    (hW3P : starImg 3 H D.W₃ ≤ starP H)
    (h₂ : ∃ x ∈ S.V, D.W₁.map (MulAut.conj x).toMonoidHom = D.W₂)
    (h₃ : ∃ x ∈ S.V, D.W₁.map (MulAut.conj x).toMonoidHom = D.W₃) :
    MulAction.stabilizer (StarGroup 3 H) (starW H D.W₁) ≤ starImg 3 H M ∧
      ¬ 3 ∣ (starImg 3 H M).index ∧
      (MulAction.orbit (StarGroup 3 H) (starW H D.W₁)).ncard ≤ 13 ∧
      3 ≤ (MulAction.orbit (starImg 3 H M) (starW H D.W₁)).ncard := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    exact mem_starImg_M_of_stabilizer hc D hW1P (MulAction.mem_stabilizer_iff.mp hy)
  · exact not_three_dvd_index_starImg_M hc D hn S
  · exact ncard_orbit_le_thirteen hE27.card hW1P hE27.card₁
  · exact three_le_ncard_orbit_starImg_M hc D hn S hW1P hW2P hW3P hWne h₂ h₃

private theorem odd_of_ncard_modEq_three {n : ℕ} (h : n ≡ 3 [MOD 2]) : Odd n := by
  rw [Nat.odd_iff]
  change n % 2 = 3 % 2 at h
  simpa using h

private theorem starW_pairwise_ne
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hWne : starImg 3 H D.W₁ ≠ starImg 3 H D.W₂ ∧
      starImg 3 H D.W₁ ≠ starImg 3 H D.W₃ ∧
      starImg 3 H D.W₂ ≠ starImg 3 H D.W₃)
    (hW1P : starImg 3 H D.W₁ ≤ starP H) (hW2P : starImg 3 H D.W₂ ≤ starP H)
    (hW3P : starImg 3 H D.W₃ ≤ starP H) :
    starW H D.W₁ ≠ starW H D.W₂ ∧ starW H D.W₁ ≠ starW H D.W₃ ∧
      starW H D.W₂ ≠ starW H D.W₃ ∧
      ({starW H D.W₁, starW H D.W₂, starW H D.W₃} :
        Set (Subgroup ↥(starP H))).ncard = 3 := by
  have h12 : starW H D.W₁ ≠ starW H D.W₂ := by
    intro h
    apply hWne.1
    have hmap := congrArg (Subgroup.map (starP H).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hW1P,
      Subgroup.map_subgroupOf_eq_of_le hW2P] at hmap
  have h13 : starW H D.W₁ ≠ starW H D.W₃ := by
    intro h
    apply hWne.2.1
    have hmap := congrArg (Subgroup.map (starP H).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hW1P,
      Subgroup.map_subgroupOf_eq_of_le hW3P] at hmap
  have h23 : starW H D.W₂ ≠ starW H D.W₃ := by
    intro h
    apply hWne.2.2
    have hmap := congrArg (Subgroup.map (starP H).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hW2P,
      Subgroup.map_subgroupOf_eq_of_le hW3P] at hmap
  refine ⟨h12, h13, h23, ?_⟩
  rw [Set.ncard_insert_of_notMem (by simp [h12, h13]),
    Set.ncard_insert_of_notMem (by simp [h23]), Set.ncard_singleton]

private theorem index_mul_orbit_ncard_eq
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hstab_le_K : MulAction.stabilizer (StarGroup 3 H) (starW H D.W₁) ≤
      starImg 3 H M) :
    (starImg 3 H M).index *
        (MulAction.orbit (starImg 3 H M) (starW H D.W₁)).ncard =
      (MulAction.orbit (StarGroup 3 H) (starW H D.W₁)).ncard := by
  have h1 : (MulAction.stabilizer (StarGroup 3 H) (starW H D.W₁)).relIndex
      (starImg 3 H M) =
      (MulAction.orbit (starImg 3 H M) (starW H D.W₁)).ncard := by
    rw [← MulAction.index_stabilizer, ← MulAction.stabilizer_subgroupOf, Subgroup.relIndex]
  have h2 := Subgroup.relIndex_mul_index hstab_le_K
  rw [h1, MulAction.index_stabilizer] at h2
  calc (starImg 3 H M).index *
      (MulAction.orbit (starImg 3 H M) (starW H D.W₁)).ncard =
      (MulAction.orbit (starImg 3 H M) (starW H D.W₁)).ncard *
        (starImg 3 H M).index := by ring
    _ = (MulAction.orbit (StarGroup 3 H) (starW H D.W₁)).ncard := h2

private theorem false_of_not_le_of_conj
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    (S : SetupData hc D hn) (hle : ¬ S.V ≤ S.R)
    (h₂ : ∃ x ∈ S.V, D.W₁.map (MulAut.conj x).toMonoidHom = D.W₂)
    (h₃ : ∃ x ∈ S.V, D.W₁.map (MulAut.conj x).toMonoidHom = D.W₃) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hRstar, hE27⟩ := starE27Config_of_not_le hc D hn S hle
  have hWne := starImg_W_pairwise_ne hc D (hc.V_inf_relPPrimeCore_eq_bot D)
  obtain ⟨hW1P, hW2P, hW3P, hcardω1⟩ := starOmega_basic hc D hE27
  obtain ⟨⟨hW1H, hW2H, hW3H⟩, -⟩ := W_le_H_and_DV D
  have hjoin := starOmega_join hc D hE27 hW1P hW2P hW3P
  haveI : IsMulCommutative ↥(starP H) := hE27.elem.1
  have hcommP : ∀ a b : ↥(starP H), a * b = b * a := fun a b =>
    setLike_mul_comm (Subgroup.mem_top a) (Subgroup.mem_top b)
  obtain ⟨hinv1, hinv2, hfix12, hfix13, hfix21, hfix23⟩ :=
    sigma_inv_fix hc D hRstar hW1H hW2H hW3H hW1P hW2P hW3P
  obtain ⟨hσ1_sq, hσ2_sq, hσcomm⟩ :=
    sigma_sq_comm hc D hjoin hcommP hinv1 hinv2 hfix12 hfix13 hfix21 hfix23
  obtain ⟨hσ1_inv_ω1, hσ1_fix_ω2, hσ1_fix_ω3, hσ2_fix_ω1, hσ2_inv_ω2, hσ2_fix_ω3⟩ :=
    sigma_smul hc D hE27 hW1P hW2P hW3P
  obtain ⟨hmemω2, hmemω3⟩ :=
    orbit_members_of_conj hc D hn S hW1P hW2P hW3P h₂ h₃
  obtain ⟨-, -, -, h3card⟩ := starW_pairwise_ne D hWne hW1P hW2P hW3P
  obtain ⟨E, hE2, -, hσ1E, hσ2E, hO, hfixω1, hfixω2, hfixω3⟩ :=
    sigma_twoGroup_fixed hc D hσ1_sq hσ2_sq hσcomm hσ1_inv_ω1 hσ1_fix_ω2 hσ1_fix_ω3
      hσ2_fix_ω1 hσ2_inv_ω2 hσ2_fix_ω3
  have hfixset := fixedPoints_orbit_eq_three hc D hE27 hσ1E hσ2E hcardω1 hmemω2 hmemω3
    hfixω1 hfixω2 hfixω3
  have hpar3 := orbit_ncard_modEq_three D hE2 hO hfixset h3card
  obtain ⟨hstab_le_K, hnot3, hle13, hge3⟩ :=
    orbit_bounds hc D hn S hE27 hWne hW1P hW2P hW3P h₂ h₃
  have hcount := index_mul_orbit_ncard_eq D hstab_le_K
  have hk1 := index_eq_one_of_orbit_count hcount hge3 hle13 hnot3
    (odd_of_ncard_modEq_three hpar3)
  exact hc.ctx.not_H_le_M (le_of_starImg_M_eq_top hc (Subgroup.index_eq_one.mp hk1))

theorem TwelveSixKCtx.false_of_starImg_le_cStarL_of_three
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃) (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hp : p = 3) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    (hY : starImg p H D.I₁ ≤ cStarL p H ∧ starImg p H D.I₂ ≤ cStarL p H ∧
      starImg p H D.I₃ ≤ cStarL p H) : False := by
  subst p
  obtain ⟨S⟩ := setupData_exists hc D rfl hn hY
  by_cases hle : S.V ≤ S.R
  · exact false_of_isSylowOf_le hc rfl S.hVsylH S.hstarR hle
  ·
    obtain ⟨u, huV, huR⟩ : ∃ u ∈ S.V, u ∉ S.R := by
      by_contra h
      apply hle
      intro x hx
      by_contra hxR
      exact h ⟨x, hx, hxR⟩
    have huDV : u ∉ D.V := fun h => huR (S.hV0R h)
    obtain ⟨h₂, h₃⟩ :=
      hc.exists_conj_eq_W₂_and_W₃ D hn S.hVM S.hV3 S.hV0V huV huDV
    exact false_of_not_le_of_conj hc D hn S hle h₂ h₃

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
