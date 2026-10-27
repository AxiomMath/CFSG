module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.QuotientCentralizer
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.StepSeven
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Lift
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFifteenOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CoreTwoL34

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped Pointwise
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem map_inf_eq_normalizer_of_l34
    {K M A : Subgroup G}
    (hK : Nonempty ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃*
      projSL 3 (GaloisField 2 2)))
    (hO : (CFSG.pPrimeCore 3 ↥K).map K.subtype ≤ M) (hKM : ¬ K ≤ M)
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K)
    (hNA : Subgroup.normalizer (A : Set G) ⊓ K ≤ M) :
    (M.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) =
      Subgroup.normalizer (((A.subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))) :
        Subgroup (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) := by
  classical
  set N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K with hNdef
  set π : ↥K →* (↥K ⧸ N) := QuotientGroup.mk' N with hπdef
  set A' : Subgroup ↥K := A.subgroupOf K with hA'def
  set Abar : Subgroup (↥K ⧸ N) := A'.map π with hAbardef
  set Y : Subgroup (↥K ⧸ N) := (M.subgroupOf K).map π with hYdef
  have hNnormal : N.Normal := hNdef ▸ CFSG.pPrimeCore_normal (p := 3) (G := ↥K)
  haveI : N.Normal := hNnormal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA'p : IsPGroup 3 ↥A' := hA'def ▸ hA.isPGroup.comap_subtype
  haveI : Fact (IsPGroup 3 ↥A') := ⟨hA'p⟩
  have hnorm : Subgroup.normalizer Abar = (Subgroup.normalizer A').map π := by
    rw [hAbardef]
    exact CFSG.normalizer_map_quotient_eq_map_normalizer 3 A' N
      (CFSG.pPrimeCore_normal (p := 3) (G := ↥K))
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K))
  have hnormA : (Subgroup.normalizer A').map K.subtype =
      Subgroup.normalizer (A : Set G) ⊓ K := by
    rw [CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer K A hA.le,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left, inf_comm]
  have hNKA_le : Subgroup.normalizer A' ≤ M.subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxG : (x : G) ∈ Subgroup.normalizer (A : Set G) := by
      have hxmap : (x : G) ∈ (Subgroup.normalizer A').map K.subtype :=
        Subgroup.mem_map_of_mem K.subtype hx
      rw [hnormA] at hxmap
      exact hxmap.1
    exact hNA ⟨hxG, x.2⟩
  have hEY : Subgroup.normalizer Abar ≤ Y := by
    rw [hnorm, hYdef]
    exact Subgroup.map_mono hNKA_le
  have hcardAbar : Nat.card Abar = 9 := by
    simpa [Abar, A', π, N] using card_map_pPrimeCore_quotient_of_isSylowOf hK hA
  have hYne : Y ≠ ⊤ := by
    intro hYtop
    apply hKM
    intro k hk
    have hkY : π ⟨k, hk⟩ ∈ Y := by
      rw [hYtop]
      exact Subgroup.mem_top _
    rw [hYdef, Subgroup.mem_map] at hkY
    obtain ⟨m, hm, hπm⟩ := hkY
    rw [Subgroup.mem_subgroupOf] at hm
    have hker : m⁻¹ * (⟨k, hk⟩ : ↥K) ∈ N := by
      have h1 : π (m⁻¹ * (⟨k, hk⟩ : ↥K)) = 1 := by
        rw [map_mul, map_inv, hπm, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (N := N) _).mp h1
    have hGM : ((m⁻¹ * (⟨k, hk⟩ : ↥K) : ↥K) : G) ∈ M :=
      hO (Subgroup.mem_map_of_mem K.subtype hker)
    have hk_eq : (k : G) = (m : G) * ((m⁻¹ * (⟨k, hk⟩ : ↥K) : ↥K) : G) := by
      simp [mul_assoc]
    rw [hk_eq]
    exact M.mul_mem hm hGM
  obtain ⟨eK⟩ := hK
  have hYeq : Y = Subgroup.normalizer Abar :=
    CFSG.RankThree.PartTwo.KFacts.L34Max.eq_normalizer_of_normalizer_le eK hcardAbar hEY hYne
  simpa [Y, Abar, A', π, N] using hYeq

variable {M E H : Subgroup G}

theorem HypCGen.conjQuotAction_map_aStar_eq
    (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hL : PLayerNotLeAt M) {A : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A (kSub 3 M H))
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M) {x : ↥H}
    (hxM : (x : G) ∈ M) :
    ((A.subgroupOf (kSub 3 M H)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))).map
        (conjQuotAction H (kSub 3 M H) (CFSG.pPrimeCore 3 ↥(kSub 3 M H))
          (kSub_le 3 M H) (hK 3 E H h) x).toMonoidHom =
      (A.subgroupOf (kSub 3 M H)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H))) := by
  classical
  let K : Subgroup G := kSub 3 M H
  let N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* (↥K ⧸ N) := QuotientGroup.mk' N
  let A' : Subgroup ↥K := A.subgroupOf K
  let Abar : Subgroup (↥K ⧸ N) := A'.map π
  let Y : Subgroup (↥K ⧸ N) := (M.subgroupOf K).map π
  let φ : MulAut (↥K ⧸ N) :=
    conjQuotAction H K N (kSub_le 3 M H) (hK 3 E H h) x
  haveI : N.Normal := CFSG.pPrimeCore_normal (p := 3) (G := ↥K)
  have hKquot : Nonempty ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃*
      projSL 3 (GaloisField 2 2)) := by
    simpa [K, threeStar] using HypCGen.nonempty_mulEquiv_threeStar hC3
  have hO : (CFSG.pPrimeCore 3 ↥K).map K.subtype ≤ M := h.pPrimeCore_map_le hK
  have hKM : ¬ K ≤ M := not_kSub_le_of_not_pLayerIn_le (p := 3) (hL 3 E H h)
  have hYeq : Y = Subgroup.normalizer Abar := by
    simpa [Y, Abar, A', π, N, K] using
      map_inf_eq_normalizer_of_l34 (K := K) (M := M) (A := A) hKquot hO hKM hA hNA
  have hcardAbar : Nat.card Abar = 9 := by
    simpa [Abar, A', π, N, K] using card_map_pPrimeCore_quotient_of_isSylowOf hKquot hA
  obtain ⟨eK⟩ := hKquot
  have hcardY : Nat.card Y = 72 := by
    rw [hYeq, CFSG.RankThree.PartTwo.KFacts.L34Max.card_normalizer_of_card_eq_nine
      eK hcardAbar]
  have hxH : (x : G) ∈ H := x.2
  have hxK : (x : G) ∈ Subgroup.normalizer (K : Set G) := hK 3 E H h hxH
  have hφY : Y.map φ.toMonoidHom ≤ Y := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨m, hm, hπm⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_subgroupOf] at hm
    have hmK : (m : G) ∈ K := m.2
    have hφy : φ (π m) = π ⟨(x : G) * (m : G) * (x : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hxK (m : G)).mp hmK⟩ :=
      conjQuotAction_apply_mk H K N (kSub_le 3 M H) (hK 3 E H h) x m
    rw [← hπm]
    change φ (π m) ∈ Y
    rw [hφy]
    refine Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ?_)
    exact M.mul_mem (M.mul_mem hxM hm) (M.inv_mem hxM)
  have hYmap : Y.map φ.toMonoidHom = Y := by
    refine Subgroup.eq_of_le_of_card_ge hφY ?_
    rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
  have hAbarY : Abar ≤ Y := Subgroup.le_normalizer.trans hYeq.symm.le
  have hAbarNormal : (Abar.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAbarY]
    exact hYeq.le
  let B : Subgroup (↥K ⧸ N) := Abar.map φ.toMonoidHom
  have hAbarP : IsPGroup 3 Abar := (hA.isPGroup.comap_subtype).map π
  have hBp : IsPGroup 3 B := hAbarP.map φ.toMonoidHom
  have hBcard : Nat.card B = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hcardAbar]
  have hBY : B ≤ Y := by
    have := Subgroup.map_mono (f := φ.toMonoidHom) hAbarY
    rwa [hYmap] at this
  have hAbarYcard : Nat.card (Abar.subgroupOf Y) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAbarY).toEquiv, hcardAbar]
  have hquotcard : Nat.card (↥Y ⧸ Abar.subgroupOf Y) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Abar.subgroupOf Y)
    rw [hAbarYcard, hcardY] at h
    omega
  let q : ↥Y →* (↥Y ⧸ Abar.subgroupOf Y) := QuotientGroup.mk' (Abar.subgroupOf Y)
  have hBq : IsPGroup 3 ((B.subgroupOf Y).map q) := (hBp.comap_subtype).map q
  have hBqcard : Nat.card ((B.subgroupOf Y).map q) = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hBq
    have hdvd : 3 ^ n ∣ 8 := by
      rw [← hn]
      simpa [hquotcard] using
        (Subgroup.card_dvd_of_le (le_top : (B.subgroupOf Y).map q ≤ ⊤))
    have hn0 : n = 0 := by
      by_contra hn0
      exact absurd ((dvd_pow_self 3 hn0).trans hdvd) (by norm_num)
    rw [hn, hn0, pow_zero]
  have hBqbot : (B.subgroupOf Y).map q = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ hBqcard
  have hBleAbar : B ≤ Abar := by
    intro b hb
    have hbY : b ∈ Y := hBY hb
    have hbq : q ⟨b, hbY⟩ ∈ (B.subgroupOf Y).map q :=
      Subgroup.mem_map_of_mem q hb
    rw [hBqbot, Subgroup.mem_bot] at hbq
    exact (QuotientGroup.eq_one_iff (N := Abar.subgroupOf Y) ⟨b, hbY⟩).mp hbq
  have hBA : B = Abar :=
    Subgroup.eq_of_le_of_card_ge hBleAbar (by rw [hBcard, hcardAbar])
  simpa [B, Abar, A', φ, π, N, K] using hBA

theorem HypCGen.inf_le_normalizer_sup_pPrimeCore
    (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hL : PLayerNotLeAt M) {A : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A (kSub 3 M H))
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M) :
    H ⊓ M ≤ Subgroup.normalizer
      (((A ⊔ (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype) :
        Subgroup G) : Set G) := by
  classical
  let K : Subgroup G := kSub 3 M H
  let N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* (↥K ⧸ N) := QuotientGroup.mk' N
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  let B : Subgroup G := A ⊔ O
  haveI : N.Normal := CFSG.pPrimeCore_normal (p := 3) (G := ↥K)
  have hOcharNorm : H ≤ Subgroup.normalizer (O : Set G) := by
    refine (hK 3 E H h).trans ?_
    simpa [O, K] using
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := K) (K := CFSG.pPrimeCore 3 ↥K))
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := by
    refine (hA.le.trans (Subgroup.le_normalizer (H := K))) |>.trans ?_
    simpa [O, K] using
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := K) (K := CFSG.pPrimeCore 3 ↥K))
  have hBeq : (B : Set G) = (A : Set G) * (O : Set G) := by
    have h := Subgroup.coe_mul_of_left_le_normalizer_right A O hAO
    simpa [B] using h
  have hconj_mem : ∀ x ∈ H ⊓ M, ∀ y ∈ B, x * y * x⁻¹ ∈ B := by
    intro x hx y hy
    change y ∈ (B : Set G) at hy
    rw [hBeq] at hy
    obtain ⟨a, ha, o, ho, rfl⟩ := hy
    have hxH : (x : G) ∈ H := hx.1
    have hxM : (x : G) ∈ M := hx.2
    have hxKnorm : (x : G) ∈ Subgroup.normalizer (K : Set G) := hK 3 E H h hxH
    have haK : a ∈ K := hA.le ha
    have hxaK : x * a * x⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hxKnorm a).mp haK
    have ha' : (⟨a, haK⟩ : ↥K) ∈ A.subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr ha
    have hφa : conjQuotAction H K N (kSub_le 3 M H) (hK 3 E H h) ⟨x, hxH⟩
        (π ⟨a, haK⟩) ∈ (A.subgroupOf K).map π := by
      have hmem := Subgroup.mem_map_of_mem
        (conjQuotAction H K N (kSub_le 3 M H) (hK 3 E H h) ⟨x, hxH⟩).toMonoidHom
        (Subgroup.mem_map_of_mem π ha')
      rwa [h.conjQuotAction_map_aStar_eq hC3 hK hL hA hNA (x := ⟨x, hxH⟩) hxM] at hmem
    obtain ⟨b, hb, hbπ⟩ := Subgroup.mem_map.mp hφa
    have hπeq : π ⟨x * a * x⁻¹, hxaK⟩ =
        conjQuotAction H K N (kSub_le 3 M H) (hK 3 E H h) ⟨x, hxH⟩
          (π ⟨a, haK⟩) := by
      simpa [π] using
        (conjQuotAction_apply_mk H K N (kSub_le 3 M H) (hK 3 E H h) ⟨x, hxH⟩
          (⟨a, haK⟩ : ↥K)).symm
    have hbA : (b : G) ∈ A := Subgroup.mem_subgroupOf.mp hb
    have hxaB : x * a * x⁻¹ ∈ B :=
      mem_sup_of_quotient_eq (K := K) (A := A) hA.le (c := ⟨x * a * x⁻¹, hxaK⟩)
        (a := (b : G)) hbA (hπeq.trans hbπ.symm)
    have hxo : x * o * x⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hOcharNorm hxH) o).mp ho
    rw [show x * (a * o) * x⁻¹ = (x * a * x⁻¹) * (x * o * x⁻¹) by group]
    exact B.mul_mem hxaB (Subgroup.mem_sup_right hxo)
  have hkey : H ⊓ M ≤ Subgroup.normalizer (B : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj_mem x hx y
    · intro hy
      have hxinv : x⁻¹ ∈ H ⊓ M := ⟨H.inv_mem hx.1, M.inv_mem hx.2⟩
      have := hconj_mem x⁻¹ hxinv (x * y * x⁻¹) hy
      simpa [mul_assoc] using this
  simpa [B, O, K] using hkey

theorem HypCGen.isPGroup_pPrimeCore_kSub
    (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hTwo : KTwoComponentAt M) :
    IsPGroup 2 ((CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype) := by
  let K : Subgroup G := kSub 3 M H
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
    simpa [K] using h.isQuasisimple_kSub_quotient hTwo
  have hL : Nonempty ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃*
      projSL 3 (GaloisField 2 2)) := by
    simpa [K, threeStar] using HypCGen.nonempty_mulEquiv_threeStar hC3
  have hEq : CFSG.pCore 2 ↥K = CFSG.pPrimeCore 3 ↥K :=
    pCore_two_eq_pPrimeCore_three hq hL
  have hp : IsPGroup 2 (CFSG.pPrimeCore 3 ↥K) := by
    rw [← hEq]
    exact CFSG.pCore_isPGroup
  simpa [K] using hp.map K.subtype

theorem HypCGen.pPrimeCore_kSub_le_of_isSylowOf
    (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hTwo : KTwoComponentAt M) (hK : KNormalAt M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype ≤ T := by
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  have hOp : IsPGroup 2 O := by
    simpa [O, K] using h.isPGroup_pPrimeCore_kSub hC3 hTwo
  have hOH : O ≤ H := (Subgroup.map_subtype_le _).trans (kSub_le 3 M H)
  have hOM : O ≤ M := by
    simpa [O, K] using h.pPrimeCore_map_le hK
  have hOHM : O ≤ H ⊓ M := le_inf hOH hOM
  have hHnormO : H ≤ Subgroup.normalizer (O : Set G) := by
    refine (hK 3 E H h).trans ?_
    simpa [O, K] using
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := K) (K := CFSG.pPrimeCore 3 ↥K))
  have hTnorm : T ≤ Subgroup.normalizer (O : Set G) :=
    hT.le.trans (inf_le_left.trans hHnormO)
  have hsupP : IsPGroup 2 (O ⊔ T : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hOp hT.isPGroup hTnorm
  have hsupLe : (O ⊔ T) ≤ H ⊓ M := sup_le hOHM hT.le
  have heq : (O ⊔ T) = T := hT.eq_of_le le_sup_right hsupLe hsupP
  exact le_sup_left.trans heq.le

theorem HypCGen.pPrimeCore_kSub_le_pCoreOf
    (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hTwo : KTwoComponentAt M) (hK : KNormalAt M) {A T : Subgroup G}
    (hAH : A ≤ H) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype ≤
      CFSG.Open.pCoreOf 2 (A ⊔ T) := by
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  have hOT : O ≤ T := h.pPrimeCore_kSub_le_of_isSylowOf hC3 hTwo hK hT
  have hOAT : O ≤ A ⊔ T := hOT.trans le_sup_right
  have hOp : IsPGroup 2 O := h.isPGroup_pPrimeCore_kSub hC3 hTwo
  have hHnormO : H ≤ Subgroup.normalizer (O : Set G) := by
    refine (hK 3 E H h).trans ?_
    simpa [O, K] using
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := K) (K := CFSG.pPrimeCore 3 ↥K))
  have hTH : T ≤ H := hT.le.trans inf_le_left
  have hATnorm : A ⊔ T ≤ Subgroup.normalizer (O : Set G) :=
    sup_le (hAH.trans hHnormO) (hTH.trans hHnormO)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOAT hATnorm hOp

theorem HypCGen.pCoreOf_sup_le_of_isSylowOf {A : Subgroup G} (h : HypCGen G M 3 A H)
    {T : Subgroup G}
    (hAH : A ≤ H) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    CFSG.Open.pCoreOf 2 (A ⊔ T) ≤ T := by
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (A ⊔ T)
  have hRp : IsPGroup 2 R :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (A ⊔ T)
  have hRH : R ≤ H :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (A ⊔ T)).trans
      (sup_le hAH (hT.le.trans inf_le_left))
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    (le_sup_left : A ≤ A ⊔ T).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
  have hRM : R ≤ M := h.invariant_two_le_M hRp hAR
  have hRHM : R ≤ H ⊓ M := le_inf hRH hRM
  have hTnorm : T ≤ Subgroup.normalizer (R : Set G) :=
    (le_sup_right : T ≤ A ⊔ T).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
  have hsupP : IsPGroup 2 (R ⊔ T : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hRp hT.isPGroup hTnorm
  have hsupLe : (R ⊔ T) ≤ H ⊓ M := sup_le hRHM hT.le
  have heq : (R ⊔ T) = T := hT.eq_of_le le_sup_right hsupLe hsupP
  exact le_sup_left.trans heq.le

theorem HypCGen.coe_mul_comm_of_isSylowOf
    {A : Subgroup G} (h : HypCGen G M 3 A H)
    (hC3 : CaseThree M H) (hTwo : KTwoComponentAt M) (hK : KNormalAt M)
    (hL : PLayerNotLeAt M) (hAK : A ≤ kSub 3 M H)
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) := by
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  let B : Subgroup G := A ⊔ O
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (A ⊔ T)
  have hA : CFSG.ABGLocalTools.IsSylowOf 3 A K := by
    simpa [K] using h.isSylowOf_three_E hC3 hAK
  have hAH : A ≤ H := hAK.trans (kSub_le 3 M H)
  have hOR : O ≤ R := by
    simpa [O, R, K] using h.pPrimeCore_kSub_le_pCoreOf hC3 hTwo hK hAH hT
  have hRT : R ≤ T := h.pCoreOf_sup_le_of_isSylowOf hAH hT
  have hOTle : O ≤ T := hOR.trans hRT
  have hTB : T ≤ Subgroup.normalizer (B : Set G) := by
    refine hT.le.trans ?_
    simpa [B, K, O] using h.inf_le_normalizer_sup_pPrimeCore hC3 hK hL hA hNA
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := by
    refine (hAK.trans (Subgroup.le_normalizer (H := K))) |>.trans ?_
    simpa [O, K] using
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := K) (K := CFSG.pPrimeCore 3 ↥K))
  have hcommBT : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) := by
    have h1 := Subgroup.coe_mul_of_right_le_normalizer_left B T hTB
    have h2 := Subgroup.coe_mul_of_left_le_normalizer_right T B hTB
    rw [sup_comm] at h2
    exact h1.symm.trans h2
  have hB_AO : (B : Set G) = (A : Set G) * (O : Set G) := by
    have h := Subgroup.coe_mul_of_left_le_normalizer_right A O hAO
    simpa [B] using h
  have hB_OA : (B : Set G) = (O : Set G) * (A : Set G) := by
    have h := Subgroup.coe_mul_of_right_le_normalizer_left O A hAO
    rw [sup_comm] at h
    simpa [B] using h
  have hOT : (O : Set G) * (T : Set G) = (T : Set G) := by
    ext x
    constructor
    · rintro ⟨o, ho, t, ht, rfl⟩
      exact T.mul_mem (hOTle ho) ht
    · intro hx
      exact ⟨1, O.one_mem, x, hx, one_mul x⟩
  have hTO : (T : Set G) * (O : Set G) = (T : Set G) := by
    ext x
    constructor
    · rintro ⟨t, ht, o, ho, rfl⟩
      exact T.mul_mem ht (hOTle ho)
    · intro hx
      exact ⟨x, hx, 1, O.one_mem, mul_one x⟩
  calc
    (A : Set G) * (T : Set G)
        = (A : Set G) * ((O : Set G) * (T : Set G)) := by rw [hOT]
    _ = ((A : Set G) * (O : Set G)) * (T : Set G) := by rw [mul_assoc]
    _ = (B : Set G) * (T : Set G) := by rw [← hB_AO]
    _ = (T : Set G) * (B : Set G) := hcommBT
    _ = (T : Set G) * ((O : Set G) * (A : Set G)) := by rw [← hB_OA]
    _ = ((T : Set G) * (O : Set G)) * (A : Set G) := by rw [mul_assoc]
    _ = (T : Set G) * (A : Set G) := by rw [hTO]

theorem HypCGen.sylowTwo_le_normalizer_sup_pCoreOf
    {A : Subgroup G} (h : HypCGen G M 3 A H)
    (hC3 : CaseThree M H) (hTwo : KTwoComponentAt M) (hK : KNormalAt M)
    (hL : PLayerNotLeAt M) (hAK : A ≤ kSub 3 M H)
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    T ≤ Subgroup.normalizer
      (((A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) : Subgroup G)) : Set G) := by
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (A ⊔ T)
  have hA : CFSG.ABGLocalTools.IsSylowOf 3 A K := by
    simpa [K] using h.isSylowOf_three_E hC3 hAK
  have hAH : A ≤ H := hAK.trans (kSub_le 3 M H)
  have hOR : O ≤ R := by
    simpa [O, R, K] using h.pPrimeCore_kSub_le_pCoreOf hC3 hTwo hK hAH hT
  have hTB : T ≤ Subgroup.normalizer (A ⊔ O : Subgroup G) := by
    refine hT.le.trans ?_
    simpa [K, O] using h.inf_le_normalizer_sup_pPrimeCore hC3 hK hL hA hNA
  have hTR : T ≤ Subgroup.normalizer (R : Set G) :=
    (le_sup_right : T ≤ A ⊔ T).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
  have hsupEq : ((A ⊔ O) ⊔ R : Subgroup G) = A ⊔ R := by
    rw [sup_assoc, sup_eq_right.mpr hOR]
  have hTBR : T ≤ Subgroup.normalizer (((A ⊔ O) ⊔ R : Subgroup G) : Set G) :=
    (le_inf hTB hTR).trans
      (Subgroup.inf_normalizer_le_normalizer_sup (A ⊔ O : Subgroup G) R)
  rwa [hsupEq] at hTBR

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
