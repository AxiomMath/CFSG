module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixSigns
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarAut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPGen
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSetup
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIData
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixInvariantX
import CFSG.ClassicalInvolution.Q3.Q3MFOU4F9

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeUC.AGL81C
variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem ne_bot_inf_of_isSylowOf_of_three_dvd {O P S : Subgroup G}
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 S P) (hOP : O ≤ P)
    (hPN : P ≤ Subgroup.normalizer (O : Set G)) (hdvd : 3 ∣ Nat.card O) :
    S ⊓ O ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSylO : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ O) O :=
    hSyl.inf_of_le_normalizer hOP hPN
  have hk : 0 < (Nat.card O).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hdvd
  intro hbot
  have h1 : 3 ^ (Nat.card O).factorization 3 = 1 := by
    rw [← hSylO.card_eq, hbot, Subgroup.card_bot]
  have h2 : 3 ≤ 3 ^ (Nat.card O).factorization 3 :=
    Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hk) 3
  omega

private theorem exists_order_three_centralizing_of_isSylowOf {O P S : Subgroup G}
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 S P) (hOP : O ≤ P)
    (hPN : P ≤ Subgroup.normalizer (O : Set G)) (hdvd : 3 ∣ Nat.card O) :
    ∃ r ∈ S ⊓ O, (∀ s ∈ S, s * r = r * s) ∧ orderOf r = 3 :=
  exists_central_order_three_of_le_normalizer hSyl.isPGroup inf_le_left
    ((le_inf Subgroup.le_normalizer (hSyl.le.trans hPN)).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
    (ne_bot_inf_of_isSylowOf_of_three_dvd hSyl hOP hPN hdvd)

private theorem not_three_dvd_card_of_isElemAbelian_e27 {V O : Subgroup G}
    (hE : IsElemAbelian 3 V) (hVcard : Nat.card V = 27) (hVO : V ⊓ O = ⊥)
    (hPN : V ⊔ O ≤ Subgroup.normalizer (O : Set G)) (hVM : V ≤ M) (hOM : O ≤ M)
    (h3 : CFSG.Open.pRank 3 M ≤ 3) : ¬ 3 ∣ Nat.card O := by
  intro hdvd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hSyl, hVS⟩ := exists_isSylowOf_ge (p := 3) (Q := V) (K := V ⊔ O) le_sup_left
    (CFSG.Open.IsElemAbelian.isPGroup hE)
  obtain ⟨r, hrS, hrcent, hrord⟩ :=
    exists_order_three_centralizing_of_isSylowOf hSyl le_sup_right hPN hdvd
  have hrO : r ∈ O := (Subgroup.mem_inf.mp hrS).2
  have hrnotV : r ∉ V := by
    intro hrV
    have h1 : r ∈ (⊥ : Subgroup G) := by
      rw [← hVO]
      exact Subgroup.mem_inf.mpr ⟨hrV, hrO⟩
    rw [Subgroup.mem_bot] at h1
    have h2 : orderOf r = 1 := by rw [h1, orderOf_one]
    omega
  have hrpow : r ^ 3 = 1 := by
    have h := pow_orderOf_eq_one r
    rwa [hrord] at h
  have hVcard3 : Nat.card V = 3 ^ 3 := by
    rw [hVcard]
    norm_num
  have hrcomm : ∀ v ∈ V, v * r = r * v := fun v hv => hrcent v (hVS hv)
  obtain ⟨hE', hEcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_sup_zpowers_of_card (p := 3) Nat.prime_three
      (E := V) hE (k := 3) hVcard3 hrpow hrnotV hrcomm
  have hEM : V ⊔ Subgroup.zpowers r ≤ M :=
    sup_le hVM (Subgroup.zpowers_le.mpr (hOM hrO))
  have h4 : 4 ≤ CFSG.Open.pRank 3 M :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hEM hE' (k := 4) (by rw [hEcard])
  omega

theorem TwelveSixKCtx.not_three_dvd_card_xSub
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hXM : xSub p M H ≤ M) :
    ¬ 3 ∣ Nat.card (xSub p M H) := by
  have hVX := hc.inf_xSub_eq_bot D.cfg (D.centralizer_le₁ hc) (D.centralizer_le₂ hc)
    (D.centralizer_le₃ hc) (D.t₁_mem hc.data) (D.t₂_mem hc.data) (D.t₃_mem hc.data)
  have hVM : D.V ≤ M := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_right
  have hVHM : D.V ≤ H ⊓ M := D.V_le.trans (D.sup_le hc.data)
  have hPN : D.V ⊔ xSub p M H ≤ Subgroup.normalizer (xSub p M H : Set G) :=
    sup_le (hVHM.trans (inf_le_normalizer_xSub p M H)) Subgroup.le_normalizer
  exact not_three_dvd_card_of_isElemAbelian_e27 D.cfg.elem D.cfg.card hVX hPN hVM hXM hc.h3

private theorem not_three_dvd_relIndex_kSub
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hp : p = 3)
    (hXM : xSub p M H ≤ M) (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hZ : center (modTwoCore (kSub p M H)) = ⊥)
    (hAut : Nat.card (MulAut (modTwoCore (kSub p M H))) ≤
      2 * Nat.card (modTwoCore (kSub p M H))) :
    ¬ 3 ∣ (kSub p M H).relIndex H := by
  subst hp
  have hX3 : ¬ 3 ∣ Nat.card (xSub 3 M H) :=
    TwelveSixKCtx.not_three_dvd_card_xSub hc D hXM
  have hKXnorm : kSub 3 M H ≤ Subgroup.normalizer (xSub 3 M H : Set G) :=
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le 3 M H).trans
      (xSub_normal_of_kSub_normal hKH)
  have hKX : ¬ 3 ∣ (kSub 3 M H).relIndex (kSub 3 M H ⊔ xSub 3 M H) := by
    rw [(CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := kSub 3 M H) (K := xSub 3 M H) hKXnorm).1]
    intro hd
    apply hX3
    rw [← Subgroup.relIndex_mul_card (H := kSub 3 M H ⊓ xSub 3 M H)
      (K := xSub 3 M H)]
    exact dvd_mul_of_dvd_left hd _
  have hKXH : ¬ 3 ∣ (kSub 3 M H ⊔ xSub 3 M H).relIndex H := by
    have hidx : ((kSub 3 M H ⊔ xSub 3 M H).subgroupOf H).index ≤ 2 :=
      TwelveCtx.index_sup_le_two hc.ctx hKH hK hZ hAut
    change ¬ 3 ∣ ((kSub 3 M H ⊔ xSub 3 M H).subgroupOf H).index
    intro hd
    have hpos : 0 < ((kSub 3 M H ⊔ xSub 3 M H).subgroupOf H).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h3le : 3 ≤ ((kSub 3 M H ⊔ xSub 3 M H).subgroupOf H).index :=
      Nat.le_of_dvd hpos hd
    omega
  have hKleH : kSub 3 M H ≤ H :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le 3 M H
  intro hd
  have hmul : (kSub 3 M H).relIndex (kSub 3 M H ⊔ xSub 3 M H) *
      (kSub 3 M H ⊔ xSub 3 M H).relIndex H = (kSub 3 M H).relIndex H :=
    Subgroup.relIndex_mul_relIndex (H := kSub 3 M H)
      (K := kSub 3 M H ⊔ xSub 3 M H) (L := H) le_sup_left
      (sup_le hKleH (xSub_le_H 3 M H))
  rw [← hmul] at hd
  exact (Nat.Prime.dvd_mul Nat.prime_three).mp hd |>.elim hKX hKXH

theorem TwelveSixKCtx.V_le_kSub
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hp : p = 3)
    (hXM : xSub p M H ≤ M) (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hZ : center (modTwoCore (kSub p M H)) = ⊥)
    (hAut : Nat.card (MulAut (modTwoCore (kSub p M H))) ≤
      2 * Nat.card (modTwoCore (kSub p M H))) :
    D.V ≤ kSub p M H := by
  subst hp
  have hVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  have hVp : IsPGroup 3 D.V := D.cfg.elem.isPGroup
  have hHnorm : H ≤ Subgroup.normalizer (kSub 3 M H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le 3 M H)).mp hKH
  exact CFSG.ABGLocalTools.le_of_isPGroup_of_not_dvd_relIndex hVp hVH
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le 3 M H) hHnorm
    (not_three_dvd_relIndex_kSub hc D rfl hXM hKH hK hZ hAut)

private theorem exists_sylow_le_kSub_normalizer
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hp : p = 3)
    (hXM : xSub p M H ≤ M) (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hZ : center (modTwoCore (kSub p M H)) = ⊥)
    (hAut : Nat.card (MulAut (modTwoCore (kSub p M H))) ≤
      2 * Nat.card (modTwoCore (kSub p M H))) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S H ∧
      S ≤ kSub p M H ∧ normalizer (S : Set G) ≤ M := by
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKleH : kSub 3 M H ≤ H :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le 3 M H
  obtain ⟨E₀, hE₀Q, hE₀, hE₀c, hΓ⟩ := hc.ctx.exists_E_sq
  have hd := hc.ctx.hypCGen hE₀Q hE₀ hE₀c hΓ
  have hU : NineNineOne M 3 :=
    hc.hI G M E₀ H E₀ 3 hd.toNineSettingGen hd.not_mem_sigmaM
  obtain ⟨S, hS, -⟩ :=
    exists_isSylowOf_ge (le_inf hc.ctx.Q_le_H hc.ctx.Q_le_M) hc.ctx.Q_isPGroup
  have hSN := isSylowOf_of_NineNineOne hc.ctx.maxLocal hc.ctx.mem_QSet hc.ctx.Q_le_H
    hd.not_mem_sigmaM hU hS
  have hSylH : CFSG.ABGLocalTools.IsSylowOf 3 S H := hSN.1
  have hNS : normalizer (S : Set G) ≤ M := hSN.2
  have hHnorm : H ≤ Subgroup.normalizer (kSub 3 M H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleH).mp hKH
  have hSK : S ≤ kSub 3 M H :=
    CFSG.ABGLocalTools.le_of_isPGroup_of_not_dvd_relIndex hSylH.isPGroup hSylH.le hKleH
      hHnorm (not_three_dvd_relIndex_kSub hc D rfl hXM hKH hK hZ hAut)
  exact ⟨S, hSylH, hSK, hNS⟩

theorem TwelveSixKCtx.sylow_kSub_inf
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hp : p = 3)
    (hXM : xSub p M H ≤ M) (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hZ : center (modTwoCore (kSub p M H)) = ⊥)
    (hAut : Nat.card (MulAut (modTwoCore (kSub p M H))) ≤
      2 * Nat.card (modTwoCore (kSub p M H)))
    {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (kSub p M H ⊓ M)) :
    CFSG.ABGLocalTools.IsSylowOf 3 P (kSub p M H) ∧
      normalizer (P : Set G) ≤ M := by
  obtain ⟨S, hSylH, hSK, hNS⟩ :=
    exists_sylow_le_kSub_normalizer hc D hp hXM hKH hK hZ hAut
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKleH : kSub p M H ≤ H :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le p M H
  have hSM : S ≤ M := (Subgroup.le_normalizer : S ≤ normalizer (S : Set G)).trans hNS
  have hSKM : S ≤ kSub p M H ⊓ M := le_inf hSK hSM
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 3 S (kSub p M H) :=
    hSylH.of_le hSK hKleH
  have hSylKM : CFSG.ABGLocalTools.IsSylowOf 3 S (kSub p M H ⊓ M) :=
    hSylK.of_le hSKM inf_le_left
  obtain ⟨k, hkKM, hconj⟩ := hSylKM.exists_mem_conj hP
  have hkM : k ∈ M := hkKM.2
  have hPmap : P = S.map (MulAut.conj k).toMonoidHom := by
    ext x
    constructor
    · intro hx
      have h : k⁻¹ * x * k ∈ S := (hconj x).mp hx
      refine Subgroup.mem_map.mpr ⟨k⁻¹ * x * k, h, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨y, hy, rfl⟩
      rw [hconj]
      change k⁻¹ * (k * y * k⁻¹) * k ∈ S
      have hre : k⁻¹ * (k * y * k⁻¹) * k = y := by group
      rwa [hre]
  have hPK : P ≤ kSub p M H := by
    rw [hPmap]
    rintro x ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hkKM.1) (y : G)).mp (hSK hy)
  have hcardP : Nat.card P = 3 ^ (Nat.card (kSub p M H)).factorization 3 := by
    rw [hPmap, Subgroup.card_map_of_injective (MulAut.conj k).injective, hSylK.card_eq]
  refine ⟨CFSG.ABGLocalTools.isSylowOf_of_card hPK hcardP, ?_⟩
  rw [hPmap, ← Subgroup.map_equiv_normalizer_eq S (MulAut.conj k)]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact M.mul_mem (M.mul_mem hkM (hNS hy)) (M.inv_mem hkM)

private theorem le_W₁ {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) : W₁ ≤ V := by
  rw [h.join]
  exact le_sup_left.trans le_sup_left

private theorem le_W₂ {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) : W₂ ≤ V := by
  rw [h.join]
  exact le_sup_right.trans le_sup_left

private theorem le_W₃ {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) : W₃ ≤ V := by
  rw [h.join]
  exact le_sup_right

private theorem not_mem_centralizer_of_inv {V W : Subgroup G} {g : G}
    (hWV : W ≤ V) (hcard : Nat.card W = 3)
    (hinv : ∀ w ∈ W, g * w * g⁻¹ = w⁻¹) :
    g ∉ centralizer (V : Set G) := by
  intro hg
  have hWne : W ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    rw [hcard]
    norm_num
  haveI : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hWne
  obtain ⟨w, hwne⟩ := exists_ne (1 : ↥W)
  have hwmem : (w : G) ∈ W := w.2
  have hcomm : g * (w : G) = (w : G) * g :=
    (Subgroup.mem_centralizer_iff.mp hg (w : G) (hWV hwmem)).symm
  have hconj : g * (w : G) * g⁻¹ = (w : G) := by
    calc g * (w : G) * g⁻¹ = ((w : G) * g) * g⁻¹ := by rw [hcomm]
      _ = (w : G) := by group
  have hweq : (w : G) = (w : G)⁻¹ := hconj.symm.trans (hinv (w : G) hwmem)
  have hw2 : (w : G) * (w : G) = 1 := by
    nth_rewrite 1 [hweq]
    exact inv_mul_cancel (w : G)
  have hw3 : (w : G) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥W) (x := w)
    rw [hcard] at h
    exact congrArg Subtype.val h
  have hw1 : (w : G) = 1 := by
    have h3 : (w : G) ^ 3 = (w : G) := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, hw2, one_mul]
    rw [← h3, hw3]
  exact hwne (Subtype.ext hw1)

private theorem t₁_not_mem_centralizer {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    t₁ ∉ centralizer (V : Set G) :=
  not_mem_centralizer_of_inv (le_W₁ h) h.card₁ h.inv₁

private theorem t₂_not_mem_centralizer {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    t₂ ∉ centralizer (V : Set G) :=
  not_mem_centralizer_of_inv (le_W₂ h) h.card₂ h.inv₂

private theorem t₃_not_mem_centralizer {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    t₃ ∉ centralizer (V : Set G) :=
  not_mem_centralizer_of_inv (le_W₃ h) h.card₃ h.inv₃

private theorem t₁_mul_t₂_not_mem_centralizer {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    t₁ * t₂ ∉ centralizer (V : Set G) := by
  refine not_mem_centralizer_of_inv (le_W₁ h) h.card₁ ?_
  intro w hw
  calc (t₁ * t₂) * w * (t₁ * t₂)⁻¹
      = t₁ * (t₂ * w * t₂⁻¹) * t₁⁻¹ := by group
    _ = t₁ * w * t₁⁻¹ := by
        rw [show t₂ * w * t₂⁻¹ = w from by
          rw [h.comm₂ w (Subgroup.mem_sup_left hw)]; group]
    _ = w⁻¹ := h.inv₁ w hw

private theorem t₁_mul_t₃_not_mem_centralizer {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    t₁ * t₃ ∉ centralizer (V : Set G) := by
  refine not_mem_centralizer_of_inv (le_W₁ h) h.card₁ ?_
  intro w hw
  calc (t₁ * t₃) * w * (t₁ * t₃)⁻¹
      = t₁ * (t₃ * w * t₃⁻¹) * t₁⁻¹ := by group
    _ = t₁ * w * t₁⁻¹ := by
        rw [show t₃ * w * t₃⁻¹ = w from by
          rw [h.comm₃ w (Subgroup.mem_sup_left hw)]; group]
    _ = w⁻¹ := h.inv₁ w hw

private theorem t₂_mul_t₃_not_mem_centralizer {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    t₂ * t₃ ∉ centralizer (V : Set G) := by
  refine not_mem_centralizer_of_inv (le_W₂ h) h.card₂ ?_
  intro w hw
  calc (t₂ * t₃) * w * (t₂ * t₃)⁻¹
      = t₂ * (t₃ * w * t₃⁻¹) * t₂⁻¹ := by group
    _ = t₂ * w * t₂⁻¹ := by
        rw [show t₃ * w * t₃⁻¹ = w from by
          rw [h.comm₃ w (Subgroup.mem_sup_right hw)]; group]
    _ = w⁻¹ := h.inv₂ w hw

private theorem t₁_mul_t₂_mul_t₃_not_mem_centralizer
    {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    t₁ * t₂ * t₃ ∉ centralizer (V : Set G) := by
  refine not_mem_centralizer_of_inv (le_W₁ h) h.card₁ ?_
  intro w hw
  calc (t₁ * t₂ * t₃) * w * (t₁ * t₂ * t₃)⁻¹
      = t₁ * (t₂ * (t₃ * w * t₃⁻¹) * t₂⁻¹) * t₁⁻¹ := by group
    _ = t₁ * (t₂ * w * t₂⁻¹) * t₁⁻¹ := by
        rw [show t₃ * w * t₃⁻¹ = w from by
          rw [h.comm₃ w (Subgroup.mem_sup_left hw)]; group]
    _ = t₁ * w * t₁⁻¹ := by
        rw [show t₂ * w * t₂⁻¹ = w from by
          rw [h.comm₂ w (Subgroup.mem_sup_left hw)]; group]
    _ = w⁻¹ := h.inv₁ w hw

private theorem t₂_mul_t₁_mul_t₃_not_mem_centralizer
    {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    t₂ * t₁ * t₃ ∉ centralizer (V : Set G) := by
  refine not_mem_centralizer_of_inv (le_W₂ h) h.card₂ ?_
  intro w hw
  calc (t₂ * t₁ * t₃) * w * (t₂ * t₁ * t₃)⁻¹
      = t₂ * (t₁ * (t₃ * w * t₃⁻¹) * t₁⁻¹) * t₂⁻¹ := by group
    _ = t₂ * (t₁ * w * t₁⁻¹) * t₂⁻¹ := by
        rw [show t₃ * w * t₃⁻¹ = w from by
          rw [h.comm₃ w (Subgroup.mem_sup_right hw)]; group]
    _ = t₂ * w * t₂⁻¹ := by
        rw [show t₁ * w * t₁⁻¹ = w from by
          rw [h.comm₁ w (Subgroup.mem_sup_left hw)]; group]
    _ = w⁻¹ := h.inv₂ w hw

private theorem t₃_mul_t₁_mul_t₂_not_mem_centralizer
    {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    t₃ * t₁ * t₂ ∉ centralizer (V : Set G) := by
  refine not_mem_centralizer_of_inv (le_W₃ h) h.card₃ ?_
  intro w hw
  calc (t₃ * t₁ * t₂) * w * (t₃ * t₁ * t₂)⁻¹
      = t₃ * (t₁ * (t₂ * w * t₂⁻¹) * t₁⁻¹) * t₃⁻¹ := by group
    _ = t₃ * (t₁ * w * t₁⁻¹) * t₃⁻¹ := by
        rw [show t₂ * w * t₂⁻¹ = w from by
          rw [h.comm₂ w (Subgroup.mem_sup_right hw)]; group]
    _ = t₃ * w * t₃⁻¹ := by
        rw [show t₁ * w * t₁⁻¹ = w from by
          rw [h.comm₁ w (Subgroup.mem_sup_right hw)]; group]
    _ = w⁻¹ := h.inv₃ w hw

private theorem t₁t₂_mul_t₁t₃_not_mem_centralizer
    {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    (t₁ * t₂) * (t₁ * t₃) ∉ centralizer (V : Set G) := by
  refine not_mem_centralizer_of_inv (le_W₂ h) h.card₂ ?_
  intro w hw
  calc ((t₁ * t₂) * (t₁ * t₃)) * w * ((t₁ * t₂) * (t₁ * t₃))⁻¹
      = t₁ * (t₂ * (t₁ * (t₃ * w * t₃⁻¹) * t₁⁻¹) * t₂⁻¹) * t₁⁻¹ := by group
    _ = t₁ * (t₂ * (t₁ * w * t₁⁻¹) * t₂⁻¹) * t₁⁻¹ := by
        rw [show t₃ * w * t₃⁻¹ = w from by
          rw [h.comm₃ w (Subgroup.mem_sup_right hw)]; group]
    _ = t₁ * (t₂ * w * t₂⁻¹) * t₁⁻¹ := by
        rw [show t₁ * w * t₁⁻¹ = w from by
          rw [h.comm₁ w (Subgroup.mem_sup_left hw)]; group]
    _ = t₁ * w⁻¹ * t₁⁻¹ := by
        rw [h.inv₂ w hw]
    _ = w⁻¹ := by
        have hc : t₁ * w⁻¹ = w⁻¹ * t₁ :=
          (Commute.inv_right (h.comm₁ w (Subgroup.mem_sup_left hw))).eq
        rw [hc]
        group


private theorem mem_sign_sub {W₁ W₂ W₃ M KX : Subgroup G} {u : G}
    (hTN : u ∈ tripleNormalizer W₁ W₂ W₃) (hM : u ∈ M) (hKX : u ∈ KX) :
    u ∈ tripleNormalizer W₁ W₂ W₃ ⊓ M ⊓ KX :=
  ⟨⟨hTN, hM⟩, hKX⟩

private theorem mul_mem_of_not_mem_of_not_mem_of_index_le_two {L H : Subgroup G}
    (hidx : (L.subgroupOf H).index ≤ 2) {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (haL : a ∉ L) (hbL : b ∉ L) : a * b ∈ L := by
  rcases lt_or_eq_of_le hidx with hlt | heq
  · have hpos : (L.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hidx1 : (L.subgroupOf H).index = 1 := by omega
    have htop : L.subgroupOf H = ⊤ := Subgroup.index_eq_one.mp hidx1
    have haL' : (⟨a, ha⟩ : ↥H) ∈ L.subgroupOf H := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (haL (Subgroup.mem_subgroupOf.mp haL')).elim
  · have h := (Subgroup.mul_mem_iff_of_index_two heq (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).mpr
      (iff_of_false (by simpa only [Subgroup.mem_subgroupOf] using haL)
        (by simpa only [Subgroup.mem_subgroupOf] using hbL))
    exact Subgroup.mem_subgroupOf.mp h

private theorem sign_base
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    (D.t₁ ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ∧
      D.t₂ ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ∧
      D.t₃ ∈ tripleNormalizer D.W₁ D.W₂ D.W₃) ∧
    (D.t₁ ∈ M ∧ D.t₂ ∈ M ∧ D.t₃ ∈ M) ∧
    (D.t₁ ∈ H ∧ D.t₂ ∈ H ∧ D.t₃ ∈ H) :=
  ⟨⟨D.cfg.t₁_mem_tripleNormalizer, D.cfg.t₂_mem_tripleNormalizer,
      D.cfg.t₃_mem_tripleNormalizer⟩,
    ⟨(D.t₁_mem hc.data).2, (D.t₂_mem hc.data).2, (D.t₃_mem hc.data).2⟩,
    ⟨(D.t₁_mem hc.data).1, (D.t₂_mem hc.data).1, (D.t₃_mem hc.data).1⟩⟩

private theorem exists_sign_pair_of_t₁_t₂
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {KX : Subgroup G}
    (hKXidx : (KX.subgroupOf H).index ≤ 2) (h1 : D.t₁ ∈ KX) (h2 : D.t₂ ∈ KX) :
    ∃ u u' : G,
      u ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u' ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u ∉ centralizer (D.V : Set G) ∧ u' ∉ centralizer (D.V : Set G) ∧
      u * u' ∉ centralizer (D.V : Set G) := by
  obtain ⟨⟨hT1, hT2, -⟩, ⟨hM1, hM2, -⟩, -⟩ := sign_base hc D
  exact ⟨D.t₁, D.t₂, mem_sign_sub hT1 hM1 h1, mem_sign_sub hT2 hM2 h2,
    t₁_not_mem_centralizer D.cfg, t₂_not_mem_centralizer D.cfg,
    t₁_mul_t₂_not_mem_centralizer D.cfg⟩

private theorem exists_sign_pair_of_t₁_t₃
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {KX : Subgroup G}
    (hKXidx : (KX.subgroupOf H).index ≤ 2) (h1 : D.t₁ ∈ KX) (h3 : D.t₃ ∈ KX) :
    ∃ u u' : G,
      u ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u' ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u ∉ centralizer (D.V : Set G) ∧ u' ∉ centralizer (D.V : Set G) ∧
      u * u' ∉ centralizer (D.V : Set G) := by
  obtain ⟨⟨hT1, -, hT3⟩, ⟨hM1, -, hM3⟩, -⟩ := sign_base hc D
  exact ⟨D.t₁, D.t₃, mem_sign_sub hT1 hM1 h1, mem_sign_sub hT3 hM3 h3,
    t₁_not_mem_centralizer D.cfg, t₃_not_mem_centralizer D.cfg,
    t₁_mul_t₃_not_mem_centralizer D.cfg⟩

private theorem exists_sign_pair_of_t₂_t₃
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {KX : Subgroup G}
    (hKXidx : (KX.subgroupOf H).index ≤ 2) (h2 : D.t₂ ∈ KX) (h3 : D.t₃ ∈ KX) :
    ∃ u u' : G,
      u ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u' ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u ∉ centralizer (D.V : Set G) ∧ u' ∉ centralizer (D.V : Set G) ∧
      u * u' ∉ centralizer (D.V : Set G) := by
  obtain ⟨⟨-, hT2, hT3⟩, ⟨-, hM2, hM3⟩, -⟩ := sign_base hc D
  exact ⟨D.t₂, D.t₃, mem_sign_sub hT2 hM2 h2, mem_sign_sub hT3 hM3 h3,
    t₂_not_mem_centralizer D.cfg, t₃_not_mem_centralizer D.cfg,
    t₂_mul_t₃_not_mem_centralizer D.cfg⟩

private theorem exists_sign_pair_of_t₁_mul_t₂_t₃
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {KX : Subgroup G}
    (hKXidx : (KX.subgroupOf H).index ≤ 2) (h1 : D.t₁ ∈ KX)
    (h2 : D.t₂ ∉ KX) (h3 : D.t₃ ∉ KX) :
    ∃ u u' : G,
      u ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u' ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u ∉ centralizer (D.V : Set G) ∧ u' ∉ centralizer (D.V : Set G) ∧
      u * u' ∉ centralizer (D.V : Set G) := by
  obtain ⟨⟨hT1, hT2, hT3⟩, ⟨hM1, hM2, hM3⟩, ⟨-, hH2, hH3⟩⟩ := sign_base hc D
  have h23K : D.t₂ * D.t₃ ∈ KX :=
    mul_mem_of_not_mem_of_not_mem_of_index_le_two hKXidx hH2 hH3 h2 h3
  have hT23 : D.t₂ * D.t₃ ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ :=
    (tripleNormalizer D.W₁ D.W₂ D.W₃).mul_mem hT2 hT3
  have hM23 : D.t₂ * D.t₃ ∈ M := M.mul_mem hM2 hM3
  refine ⟨D.t₁, D.t₂ * D.t₃, mem_sign_sub hT1 hM1 h1, mem_sign_sub hT23 hM23 h23K,
    t₁_not_mem_centralizer D.cfg, t₂_mul_t₃_not_mem_centralizer D.cfg, ?_⟩
  simpa only [mul_assoc] using t₁_mul_t₂_mul_t₃_not_mem_centralizer D.cfg

private theorem exists_sign_pair_of_t₂_mul_t₁_t₃
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {KX : Subgroup G}
    (hKXidx : (KX.subgroupOf H).index ≤ 2) (h1 : D.t₁ ∉ KX)
    (h2 : D.t₂ ∈ KX) (h3 : D.t₃ ∉ KX) :
    ∃ u u' : G,
      u ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u' ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u ∉ centralizer (D.V : Set G) ∧ u' ∉ centralizer (D.V : Set G) ∧
      u * u' ∉ centralizer (D.V : Set G) := by
  obtain ⟨⟨hT1, hT2, hT3⟩, ⟨hM1, hM2, hM3⟩, ⟨hH1, -, hH3⟩⟩ := sign_base hc D
  have h13K : D.t₁ * D.t₃ ∈ KX :=
    mul_mem_of_not_mem_of_not_mem_of_index_le_two hKXidx hH1 hH3 h1 h3
  have hT13 : D.t₁ * D.t₃ ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ :=
    (tripleNormalizer D.W₁ D.W₂ D.W₃).mul_mem hT1 hT3
  have hM13 : D.t₁ * D.t₃ ∈ M := M.mul_mem hM1 hM3
  refine ⟨D.t₂, D.t₁ * D.t₃, mem_sign_sub hT2 hM2 h2, mem_sign_sub hT13 hM13 h13K,
    t₂_not_mem_centralizer D.cfg, t₁_mul_t₃_not_mem_centralizer D.cfg, ?_⟩
  simpa only [mul_assoc] using t₂_mul_t₁_mul_t₃_not_mem_centralizer D.cfg

private theorem exists_sign_pair_of_t₃_mul_t₁_t₂
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {KX : Subgroup G}
    (hKXidx : (KX.subgroupOf H).index ≤ 2) (h1 : D.t₁ ∉ KX)
    (h2 : D.t₂ ∉ KX) (h3 : D.t₃ ∈ KX) :
    ∃ u u' : G,
      u ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u' ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u ∉ centralizer (D.V : Set G) ∧ u' ∉ centralizer (D.V : Set G) ∧
      u * u' ∉ centralizer (D.V : Set G) := by
  obtain ⟨⟨hT1, hT2, hT3⟩, ⟨hM1, hM2, hM3⟩, ⟨hH1, hH2, -⟩⟩ := sign_base hc D
  have h12K : D.t₁ * D.t₂ ∈ KX :=
    mul_mem_of_not_mem_of_not_mem_of_index_le_two hKXidx hH1 hH2 h1 h2
  have hT12 : D.t₁ * D.t₂ ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ :=
    (tripleNormalizer D.W₁ D.W₂ D.W₃).mul_mem hT1 hT2
  have hM12 : D.t₁ * D.t₂ ∈ M := M.mul_mem hM1 hM2
  refine ⟨D.t₃, D.t₁ * D.t₂, mem_sign_sub hT3 hM3 h3, mem_sign_sub hT12 hM12 h12K,
    t₃_not_mem_centralizer D.cfg, t₁_mul_t₂_not_mem_centralizer D.cfg, ?_⟩
  simpa only [mul_assoc] using t₃_mul_t₁_mul_t₂_not_mem_centralizer D.cfg

private theorem exists_sign_pair_of_t₁t₂_mul_t₁t₃
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {KX : Subgroup G}
    (hKXidx : (KX.subgroupOf H).index ≤ 2) (h1 : D.t₁ ∉ KX)
    (h2 : D.t₂ ∉ KX) (h3 : D.t₃ ∉ KX) :
    ∃ u u' : G,
      u ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u' ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ KX ∧
      u ∉ centralizer (D.V : Set G) ∧ u' ∉ centralizer (D.V : Set G) ∧
      u * u' ∉ centralizer (D.V : Set G) := by
  obtain ⟨⟨hT1, hT2, hT3⟩, ⟨hM1, hM2, hM3⟩, ⟨hH1, hH2, hH3⟩⟩ := sign_base hc D
  have h12K : D.t₁ * D.t₂ ∈ KX :=
    mul_mem_of_not_mem_of_not_mem_of_index_le_two hKXidx hH1 hH2 h1 h2
  have h13K : D.t₁ * D.t₃ ∈ KX :=
    mul_mem_of_not_mem_of_not_mem_of_index_le_two hKXidx hH1 hH3 h1 h3
  have hT12 : D.t₁ * D.t₂ ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ :=
    (tripleNormalizer D.W₁ D.W₂ D.W₃).mul_mem hT1 hT2
  have hT13 : D.t₁ * D.t₃ ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ :=
    (tripleNormalizer D.W₁ D.W₂ D.W₃).mul_mem hT1 hT3
  have hM12 : D.t₁ * D.t₂ ∈ M := M.mul_mem hM1 hM2
  have hM13 : D.t₁ * D.t₃ ∈ M := M.mul_mem hM1 hM3
  refine ⟨D.t₁ * D.t₂, D.t₁ * D.t₃,
    mem_sign_sub hT12 hM12 h12K, mem_sign_sub hT13 hM13 h13K,
    t₁_mul_t₂_not_mem_centralizer D.cfg, t₁_mul_t₃_not_mem_centralizer D.cfg, ?_⟩
  exact t₁t₂_mul_t₁t₃_not_mem_centralizer D.cfg

theorem TwelveSixKCtx.exists_sign_pair
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hZ : center (modTwoCore (kSub p M H)) = ⊥)
    (hAut : Nat.card (MulAut (modTwoCore (kSub p M H))) ≤
      2 * Nat.card (modTwoCore (kSub p M H))) :
    ∃ u u' : G,
      u ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ (kSub p M H ⊔ xSub p M H) ∧
      u' ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ (kSub p M H ⊔ xSub p M H) ∧
      u ∉ centralizer (D.V : Set G) ∧ u' ∉ centralizer (D.V : Set G) ∧
      u * u' ∉ centralizer (D.V : Set G) := by
  let KX : Subgroup G := kSub p M H ⊔ xSub p M H
  have hKXidx : (KX.subgroupOf H).index ≤ 2 :=
    TwelveCtx.index_sup_le_two hc.ctx hKH hK hZ hAut
  by_cases h1 : D.t₁ ∈ KX
  · by_cases h2 : D.t₂ ∈ KX
    · exact exists_sign_pair_of_t₁_t₂ hc D hKXidx h1 h2
    · by_cases h3 : D.t₃ ∈ KX
      · exact exists_sign_pair_of_t₁_t₃ hc D hKXidx h1 h3
      · exact exists_sign_pair_of_t₁_mul_t₂_t₃ hc D hKXidx h1 h2 h3
  · by_cases h2 : D.t₂ ∈ KX
    · by_cases h3 : D.t₃ ∈ KX
      · exact exists_sign_pair_of_t₂_t₃ hc D hKXidx h2 h3
      · exact exists_sign_pair_of_t₂_mul_t₁_t₃ hc D hKXidx h1 h2 h3
    · by_cases h3 : D.t₃ ∈ KX
      · exact exists_sign_pair_of_t₃_mul_t₁_t₂ hc D hKXidx h1 h2 h3
      · exact exists_sign_pair_of_t₁t₂_mul_t₁t₃ hc D hKXidx h1 h2 h3

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
