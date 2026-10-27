module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Commute

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem le_oddCoreIn_of_le_normalizer {N X : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreIn X := by
  have hn : (N.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
  have hodd' : Odd (Nat.card (N.subgroupOf X)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hNX).toEquiv]
  have hle := CFSG.ComponentClassification.Asc76.L26.le_oddCore hn hodd'
  intro n hn'
  exact ⟨⟨n, hNX hn'⟩, hle hn', rfl⟩

theorem oddCoreIn_normalizer_le_centralizer {W : Subgroup G} (hW : IsPGroup 2 W) :
    oddCoreIn (normalizer (W : Set G)) ≤ centralizer (W : Set G) := by
  intro o ho
  rw [mem_centralizer_iff]
  intro w hw
  have hinf : oddCoreIn (normalizer (W : Set G)) ⊓ W = ⊥ := oddCoreIn_inf_eq_bot hW
  exact (CFSG.ComponentClassification.Asc76.L26.commute_of_inf_eq_bot hinf ho hw
    (oddCoreIn_le _ ho)
    (le_normalizer_oddCoreIn (normalizer (W : Set G)) (le_normalizer hw))).symm

omit [Finite G] in
theorem subgroupOf_le_comap_pCore {W U : Subgroup G} (hW : IsPGroup 2 W) (hUW : U ≤ W) :
    U.subgroupOf (normalizer (W : Set G)) ≤
      (CFSG.pCore 2 (normalizer (W : Set G) ⧸
        CFSG.Assembly.oddCore (normalizer (W : Set G)))).comap
        (QuotientGroup.mk' (CFSG.Assembly.oddCore (normalizer (W : Set G)))) := by
  set N := normalizer (W : Set G)
  have hWn : (W.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl
  have hW2 : IsPGroup 2 (W.subgroupOf N) := hW.comap_subtype
  have himg : (W.subgroupOf N).map (QuotientGroup.mk' (CFSG.Assembly.oddCore N)) ≤
      CFSG.pCore 2 (N ⧸ CFSG.Assembly.oddCore N) :=
    le_sSup ⟨hWn.map _ (QuotientGroup.mk'_surjective _), hW2.map _⟩
  intro u hu
  exact himg ⟨u, hUW hu, rfl⟩

theorem oddCoreIn_inf_normalizer_le (hΩ : Assumption41 Ω) {K R U W : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylowOf 2 R K) (hU : IsDihedralRot U R) (hW : IsPGroup 2 W) (hUW : U ≤ W) :
    oddCoreIn K ⊓ normalizer (W : Set G) ≤ oddCoreIn (normalizer (W : Set G)) := by
  set X := oddCoreIn K ⊓ normalizer (W : Set G) with hX
  have hUK : U ≤ K := hU.le.trans hR.le
  have hU2 : IsPGroup 2 U := hU.isPGroup.to_le hU.le
  have hUbot : U ≠ ⊥ := fun h => by
    have := hU.four_le
    rw [h, card_bot] at this
    omega
  have hXU : X ≤ normalizer (U : Set G) := by
    intro x hx
    apply CFSG.ComponentClassification.Asc76.L26.mem_normalizer_of_commute
    intro u hu
    exact (CFSG.ComponentClassification.Asc76.L26.commute_of_inf_eq_bot
      (oddCoreIn_inf_eq_bot hW) (mem_inf.mp hx).1 (hUW hu) (mem_inf.mp hx).2
      (le_normalizer_oddCoreIn K (hUK hu))).symm
  have hYX : normalizer (W : Set G) ⊓ normalizer (U : Set G) ≤ normalizer (X : Set G) := by
    intro y hy
    obtain ⟨hyW, hyU⟩ := mem_inf.mp hy
    have hyK : y ∈ normalizer (K : Set G) :=
      normalizer_two_subgroup_le K U (Assumption41.tightlyEmbedded hΩ hK) hU2 hUK hUbot hyU
    exact inf_le_normalizer_inf (mem_inf.mpr
      ⟨normalizer_le_normalizer_oddCoreIn K hyK, le_normalizer hyW⟩)
  have hXodd : Odd (Nat.card X) :=
    (odd_card_oddCoreIn K).of_dvd_nat (card_dvd_of_le inf_le_left)
  have h1 : X ≤ oddCoreIn (normalizer (W : Set G) ⊓ normalizer (U : Set G)) :=
    le_oddCoreIn_of_le_normalizer (le_inf inf_le_right hXU) hYX hXodd
  exact h1.trans (CFSG.ComponentClassification.Asc76.L26.lemma29_subgroup
    (hUW.trans le_normalizer) hU2 (subgroupOf_le_comap_pCore hW hUW))

@[expose] def IsTwoNil (K R : Subgroup G) : Prop :=
  ∀ k ∈ K, ∃ o ∈ oddCoreIn K, ∃ r ∈ R, k = o * r

theorem exists_oddCore_normalizes {K R W A : Subgroup G} (hR : IsSylowOf 2 R K)
    (hnil : IsTwoNil K R) (hRW : R ≤ normalizer (W : Set G)) (hA : IsPGroup 2 A)
    (hAK : A ≤ normalizer (K : Set G)) (hAW : A ≤ normalizer (W : Set G)) :
    ∃ o ∈ oddCoreIn K ⊓ normalizer (W : Set G),
      A ≤ normalizer ((AschbacherTightEmbedding.rightConjugate R o⁻¹ : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := K ⊓ normalizer (W : Set G)
  have hAM : A ≤ normalizer (M : Set G) := fun a ha =>
    inf_le_normalizer_inf (mem_inf.mpr ⟨hAK ha, le_normalizer (hAW ha)⟩)
  have hRM : IsSylowOf 2 R M := hR.of_le (le_inf hR.le hRW) inf_le_left
  obtain ⟨R₁, hR₁, hAR₁⟩ := exists_isSylowOf_normalized hA hAM
  obtain ⟨c, hcM, hc⟩ := CFSG.ComponentClassification.Asc76.L26.IsSylowOf.exists_conj_mem hRM hR₁
  obtain ⟨o, ho, r₀, hr₀, rfl⟩ := hnil c (mem_inf.mp hcM).1
  have hoW : o ∈ normalizer (W : Set G) := by
    have : o = o * r₀ * r₀⁻¹ := by group
    rw [this]
    exact mul_mem (mem_inf.mp hcM).2 (inv_mem (hRW hr₀))
  refine ⟨o, mem_inf.mpr ⟨ho, hoW⟩, ?_⟩
  have hR₁eq : R₁ = AschbacherTightEmbedding.rightConjugate R o⁻¹ := by
    ext x
    rw [hc, mem_rightConjugate_iff, inv_inv]
    constructor
    · intro h
      have := mul_mem (mul_mem hr₀ h) (inv_mem hr₀)
      simpa [mul_assoc] using this
    · intro h
      have := mul_mem (mul_mem (inv_mem hr₀) h) hr₀
      simpa [mul_assoc] using this
  rw [← hR₁eq]
  exact hAR₁

theorem conj_eq_mul_of_not_sylow (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω)
    {K J R T U V W : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (hR : IsSylowOf 2 R K)
    (hT : IsSylowOf 2 T J) (hU : IsDihedralRot U R) (hV : IsDihedralRot V T)
    (hnil : IsTwoNil K R) (hRW : R ≤ normalizer (W : Set G)) (hW2 : IsPGroup 2 W)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hUW : U ≤ W) (hVW : V ≤ W)
    (hnot : ¬ T ≤ normalizer (K : Set G)) {t z : G} (htV : t ∈ V) (ht1 : t ≠ 1) (htt : t * t = 1)
    (hzU : z ∈ U) (hzuniq : ∀ y ∈ U, y * y = 1 → y = 1 ∨ y = z) {x : G} (hxR : x ∈ R)
    (hxU : x ∉ U) : x⁻¹ * t * x = t * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htW : t ∈ W := hVW htV
  have htU : ∀ u ∈ U, u * t = t * u := fun u hu => hWab u (hUW hu) t htW
  have hU2 : IsPGroup 2 U := hU.isPGroup.to_le hU.le
  have hUbot : U ≠ ⊥ := fun h => by
    have := hU.four_le
    rw [h, card_bot] at this
    omega
  have hA : IsPGroup 2 (zpowers t) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact htt)
  have htK : t ∈ normalizer (K : Set G) :=
    centralizer_two_subgroup_le K U (Assumption41.tightlyEmbedded hΩ hK) hU2
      (hU.le.trans hR.le) hUbot (mem_centralizer_iff.mpr htU)
  obtain ⟨o, ho, hAR₁⟩ := exists_oddCore_normalizes hR hnil hRW hA ((zpowers_le).mpr htK)
    ((zpowers_le).mpr (le_normalizer htW))
  have hoC : o ∈ centralizer (W : Set G) := oddCoreIn_normalizer_le_centralizer hW2
    (oddCoreIn_inf_normalizer_le hΩ hK hR hU hW2 hUW ho)
  have hot : o * t = t * o := ((mem_centralizer_iff.mp hoC) t htW).symm
  set R₁ := AschbacherTightEmbedding.rightConjugate R o⁻¹ with hR₁def
  have hoU : o⁻¹ ∈ normalizer (U : Set G) :=
    Subgroup.centralizer_le_normalizer _ (inv_mem (centralizer_le hUW hoC))
  have hU₁ : IsDihedralRot U R₁ := by
    have h1 := hU.rightConjugate o⁻¹
    rwa [(rightConjugate_eq_self_iff U o⁻¹).mpr hoU] at h1
  have hR₁U : R₁ ≤ normalizer (U : Set G) := le_normalizer.trans hU₁.normalizer_le
  set y := o * x * o⁻¹ with hy
  have hyR : y ∈ R₁ := by rw [mem_rightConjugate_iff, inv_inv]; simpa [hy, mul_assoc] using hxR
  have hyU : y ∉ U := fun h => hxU (by
    have := (mem_normalizer_iff.mp hoU y).mp h
    simpa [hy, mul_assoc] using this)
  set r₁ := t⁻¹ * (y⁻¹ * t * y) with hr₁
  have htR₁ : t⁻¹ ∈ normalizer (R₁ : Set G) := inv_mem (hAR₁ (mem_zpowers t))
  have hr₁R : r₁ ∈ R₁ := by
    have h1 : t⁻¹ * y⁻¹ * t⁻¹⁻¹ ∈ R₁ := (mem_normalizer_iff.mp htR₁ _).mp (inv_mem hyR)
    have : r₁ = (t⁻¹ * y⁻¹ * t⁻¹⁻¹) * y := by rw [hr₁]; group
    rw [this]
    exact mul_mem h1 hyR
  have hr₁c : ∀ u ∈ U, r₁ * u = u * r₁ := by
    intro u hu
    have hyu : y * u * y⁻¹ ∈ U := (mem_normalizer_iff.mp (hR₁U hyR) u).mp hu
    have e1 : y⁻¹ * t * y * u = u * (y⁻¹ * t * y) := by
      calc y⁻¹ * t * y * u = y⁻¹ * (t * (y * u * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * u * y⁻¹) * t) * y := by rw [htU _ hyu]
        _ = u * (y⁻¹ * t * y) := by group
    have e2 : t⁻¹ * u = u * t⁻¹ := by
      calc t⁻¹ * u = t⁻¹ * (u * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * u) * t⁻¹ := by rw [htU u hu]
        _ = u * t⁻¹ := by group
    calc r₁ * u = t⁻¹ * (y⁻¹ * t * y * u) := by rw [hr₁]; group
      _ = t⁻¹ * u * (y⁻¹ * t * y) := by rw [e1]; group
      _ = u * r₁ := by rw [e2, hr₁]; group
  have hr₁U : r₁ ∈ U := hU₁.mem_of_commute hr₁R hr₁c
  have hr₁t : r₁ * t = t * r₁ := htU r₁ hr₁U
  have hr₁r₁ : r₁ * r₁ = 1 := by
    have h1 : (y⁻¹ * t * y) * (y⁻¹ * t * y) = 1 := by
      calc (y⁻¹ * t * y) * (y⁻¹ * t * y) = y⁻¹ * (t * t) * y := by group
        _ = 1 := by rw [htt]; group
    have h2 : y⁻¹ * t * y = t * r₁ := by rw [hr₁]; group
    rw [h2] at h1
    calc r₁ * r₁ = t * t * (r₁ * r₁) := by rw [htt, one_mul]
      _ = t * (r₁ * t) * r₁ := by rw [hr₁t]; group
      _ = (t * r₁) * (t * r₁) := by group
      _ = 1 := h1
  have hyt : y⁻¹ * t * y = t * r₁ := by rw [hr₁]; group
  rcases hzuniq r₁ hr₁U hr₁r₁ with h1 | h1
  ·
    exfalso
    rw [h1, mul_one] at hyt
    have hCJ : centralizer ({t} : Set G) ≤ normalizer (J : Set G) :=
      centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJ) (hV.le.trans hT.le htV) ht1
        htt
    have hyC : y ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc y * t = y * (y⁻¹ * t * y) := by rw [hyt]
        _ = t * y := by group
    have hUC : ∀ u ∈ U, u ∈ centralizer ({t} : Set G) := fun u hu =>
      mem_centralizer_singleton_iff.mpr (htU u hu)
    have hR₁J : R₁ ≤ normalizer (J : Set G) := by
      intro w hw
      by_cases hwU : w ∈ U
      · exact hCJ (hUC w hwU)
      · have hyw : y⁻¹ * w ∈ U := hU₁.mul_mem_of_not_mem (inv_mem hyR) hw
          (fun h => hyU (by simpa using inv_mem h)) hwU
        have : w = y * (y⁻¹ * w) := by group
        rw [this]
        exact mul_mem (hCJ hyC) (hCJ (hUC _ hyw))
    have hR₁K : IsSylowOf 2 R₁ K := by
      have h2 := isSylowOf_rightConjugate hR o⁻¹
      rwa [(rightConjugate_eq_self_iff K o⁻¹).mpr
        (le_normalizer (inv_mem (oddCoreIn_le K (mem_inf.mp ho).1)))] at h2
    obtain ⟨-, hJK⟩ := le_normalizer_of_sylow h22 hΩ hJ hK (Ne.symm hKJ) hR₁K hR₁J
    exact hnot (hT.le.trans hJK)
  ·
    rw [h1] at hyt
    have hzW : z ∈ W := hUW hzU
    have hoz : o * (t * z) = (t * z) * o :=
      ((mem_centralizer_iff.mp hoC) _ (mul_mem htW hzW)).symm
    calc x⁻¹ * t * x = o⁻¹ * (y⁻¹ * (o * t * o⁻¹) * y) * o := by rw [hy]; group
      _ = o⁻¹ * (y⁻¹ * t * y) * o := by rw [hot]; group
      _ = o⁻¹ * ((t * z) * o) := by rw [hyt]; group
      _ = t * z := by rw [← hoz]; group

omit [Finite G] in
theorem conj_mem_centralizer {W : Subgroup G} {g c : G} (hg : g ∈ normalizer (W : Set G))
    (hc : c ∈ centralizer (W : Set G)) : g * c * g⁻¹ ∈ centralizer (W : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro w hw
  have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ W := (mem_normalizer_iff.mp (inv_mem hg) w).mp hw
  have h1 := hc _ hw'
  simp only [inv_inv] at h1
  calc w * (g * c * g⁻¹) = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * w := by group

theorem commutator_mem_centralizer (hΩ : Assumption41 Ω) {K J R U W : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hKJ : K ≠ J) (hR : IsSylowOf 2 R K) (hU : IsDihedralRot U R)
    (hW2 : IsPGroup 2 W) (hUW : U ≤ W) (hJK : J ≤ normalizer (K : Set G))
    (hKJ' : K ≤ normalizer (J : Set G)) {r s : G} (hrK : r ∈ K) (hsJ : s ∈ J)
    (hrW : r ∈ normalizer (W : Set G)) (hsW : s ∈ normalizer (W : Set G)) :
    r * s * r⁻¹ * s⁻¹ ∈ centralizer (W : Set G) := by
  have hc := CFSG.ComponentClassification.Asc76.L26.commutatorElement_mem_inf hrK hsJ (hKJ' hrK)
    (hJK hsJ)
  have hKJn : K ≤ normalizer ((K ⊓ J : Subgroup G) : Set G) := fun k hk =>
    inf_le_normalizer_inf (mem_inf.mpr ⟨le_normalizer hk, hKJ' hk⟩)
  have hO : r * s * r⁻¹ * s⁻¹ ∈ oddCoreIn K :=
    le_oddCoreIn_of_le_normalizer inf_le_left hKJn (hΩ.inter K hK J hJ hKJ) hc
  have hN : r * s * r⁻¹ * s⁻¹ ∈ normalizer (W : Set G) :=
    mul_mem (mul_mem (mul_mem hrW hsW) (inv_mem hrW)) (inv_mem hsW)
  exact oddCoreIn_normalizer_le_centralizer hW2
    (oddCoreIn_inf_normalizer_le hΩ hK hR hU hW2 hUW (mem_inf.mpr ⟨hO, hN⟩))

theorem pow_three_mem_centralizer (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω)
    {K J R T U V W : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (hR : IsSylowOf 2 R K)
    (hT : IsSylowOf 2 T J) (hU : IsDihedralRot U R) (hV : IsDihedralRot V T)
    (hnilK : IsTwoNil K R) (hnilJ : IsTwoNil J T) (hRW : R ≤ normalizer (W : Set G))
    (hTW : T ≤ normalizer (W : Set G)) (hW2 : IsPGroup 2 W)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hUW : U ≤ W) (hVW : V ≤ W)
    (hnot : ¬ T ≤ normalizer (K : Set G)) {r s : G} (hrR : r ∈ R) (hrU : r ∉ U) (hsT : s ∈ T)
    (hsV : s ∉ V) : (r * s) ^ 3 ∈ centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzU, hz1, hzz, hzuniq, -⟩ := hU.exists_involution
  obtain ⟨t, htV, ht1, htt, htuniq, htc⟩ := hV.exists_involution
  have hnot' : ¬ R ≤ normalizer (J : Set G) := fun h =>
    hnot (hT.le.trans (le_normalizer_of_sylow h22 hΩ hJ hK (Ne.symm hKJ) hR h).2)
  have htr := conj_eq_mul_of_not_sylow h22 hΩ hK hJ hKJ hR hT hU hV hnilK hRW hW2 hWab hUW hVW
    hnot htV ht1 htt hzU hzuniq hrR hrU
  have hzs := conj_eq_mul_of_not_sylow h22 hΩ hJ hK (Ne.symm hKJ) hT hR hV hU hnilJ hTW hW2 hWab
    hVW hUW hnot' hzU hz1 hzz htV htuniq hsT hsV
  have hts : s⁻¹ * t * s = t := by rw [mul_assoc, ← htc s hsT]; group
  have hzt : z * t = t * z := hWab z (hUW hzU) t (hVW htV)
  set g := r * s with hg
  have hgt : g⁻¹ * t * g = z := by
    calc g⁻¹ * t * g = s⁻¹ * (r⁻¹ * t * r) * s := by rw [hg]; group
      _ = (s⁻¹ * t * s) * (s⁻¹ * z * s) := by rw [htr]; group
      _ = z := by rw [hts, hzs, ← mul_assoc, ← hzt, mul_assoc, htt, mul_one]
  have hzJ : z ∈ AschbacherTightEmbedding.rightConjugate J g := by
    rw [mem_rightConjugate_iff, ← hgt]
    simpa [mul_assoc] using hV.le.trans hT.le htV
  have hKeq : K = AschbacherTightEmbedding.rightConjugate J g := by
    by_contra hne
    have h2 : IsPGroup 2 (zpowers z) :=
      isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact hzz)
    have h3 := Assumption41.inf_eq_bot hΩ hK (hΩ.conj_mem J hJ g) hne h2
      ((zpowers_le).mpr (hU.le.trans hR.le hzU)) ((zpowers_le).mpr hzJ)
    rw [inf_idem, zpowers_eq_bot] at h3
    exact hz1 h3
  set s'' := g⁻¹ * s * g with hs''
  have hs''K : s'' ∈ K := by
    rw [hKeq, mem_rightConjugate_iff]
    simpa [hs'', mul_assoc] using hT.le hsT
  have hgW : g ∈ normalizer (W : Set G) := mul_mem (hRW hrR) (hTW hsT)
  have hs''W : s'' ∈ normalizer (W : Set G) := mul_mem (mul_mem (inv_mem hgW) (hTW hsT)) hgW
  obtain ⟨o, ho, r'', hr'', hs''eq⟩ := hnilK s'' hs''K
  have hoW : o ∈ normalizer (W : Set G) := by
    have : o = s'' * r''⁻¹ := by rw [hs''eq]; group
    rw [this]
    exact mul_mem hs''W (inv_mem (hRW hr''))
  have hoC : o ∈ centralizer (W : Set G) := oddCoreIn_normalizer_le_centralizer hW2
    (oddCoreIn_inf_normalizer_le hΩ hK hR hU hW2 hUW (mem_inf.mpr ⟨ho, hoW⟩))
  have hWC : W ≤ centralizer (W : Set G) := fun a ha =>
    mem_centralizer_iff.mpr fun b hb => hWab b hb a ha
  have hr''U : r'' ∉ U := by
    intro hr''U
    have hs''C : s'' ∈ centralizer (W : Set G) := by
      rw [hs''eq]
      exact mul_mem hoC (hWC (hUW hr''U))
    obtain ⟨ρ, hρ, hρo⟩ := hV.exists_gen
    have hρV : ρ ∈ V := hρ ▸ mem_zpowers ρ
    have hinv := hV.conj_eq s hsT hsV ρ hρV
    have hw : g⁻¹ * ρ * g ∈ W := by
      have := (mem_normalizer_iff.mp (inv_mem hgW) ρ).mp (hVW hρV)
      simpa using this
    have h1 : s'' * (g⁻¹ * ρ * g) * s''⁻¹ = (g⁻¹ * ρ * g)⁻¹ := by
      calc s'' * (g⁻¹ * ρ * g) * s''⁻¹ = g⁻¹ * (s * ρ * s⁻¹) * g := by rw [hs'']; group
        _ = (g⁻¹ * ρ * g)⁻¹ := by rw [hinv]; group
    have h2 : s'' * (g⁻¹ * ρ * g) * s''⁻¹ = g⁻¹ * ρ * g := by
      rw [← (mem_centralizer_iff.mp hs''C) _ hw]; group
    apply hV.gen_mul_self_ne_one hρo
    have h3 : (g⁻¹ * ρ * g) * (g⁻¹ * ρ * g) = 1 := by
      calc (g⁻¹ * ρ * g) * (g⁻¹ * ρ * g) = (g⁻¹ * ρ * g)⁻¹ * (g⁻¹ * ρ * g) := by
            rw [← h1, h2]
        _ = 1 := inv_mul_cancel _
    calc ρ * ρ = g * ((g⁻¹ * ρ * g) * (g⁻¹ * ρ * g)) * g⁻¹ := by group
      _ = 1 := by rw [h3]; group
  have hrr : r * r = 1 := hU.mul_self r hrR hrU
  have hss : s * s = 1 := hV.mul_self s hsT hsV
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hu : r⁻¹ * r'' ∈ U := hU.mul_mem_of_not_mem (inv_mem hrR) hr''
    (fun h => hrU (by simpa using inv_mem h)) hr''U
  have hru : r * (r⁻¹ * r'') * r⁻¹ ∈ U :=
    (mem_normalizer_iff.mp (hU.normalizer_le (le_normalizer hrR)) _).mp hu
  have h4 : s'' * r ∈ centralizer (W : Set G) := by
    have : s'' * r = o * (r * (r⁻¹ * r'') * r⁻¹) := by
      rw [hs''eq, show r * (r⁻¹ * r'') * r⁻¹ = r'' * r⁻¹ by group, hrinv, mul_assoc]
    rw [this]
    exact mul_mem hoC (hWC (hUW hru))
  have h5 : s'' * r = (s * r) ^ 3 := by
    rw [hs'', hg, show (s * r) ^ 3 = s * r * s * r * s * r by rw [pow_three]; group,
      mul_inv_rev, hsinv, hrinv]
    group
  have h6 : (r * s) ^ 3 = r * (s * r) ^ 3 * r⁻¹ := by rw [pow_three, pow_three]; group
  rw [h6, ← h5]
  exact conj_mem_centralizer (hRW hrR) h4

omit [Finite G] in
theorem not_mem_centralizer {R U W : Subgroup G} (hU : IsDihedralRot U R) (hUW : U ≤ W) {r : G}
    (hrR : r ∈ R) (hrU : r ∉ U) : r ∉ centralizer (W : Set G) := fun h =>
  hrU (hU.mem_of_commute hrR fun u hu => ((mem_centralizer_iff.mp h) u (hUW hu)).symm)

theorem mem_centralizer_or (hΩ : Assumption41 Ω) {K R U W : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylowOf 2 R K) (hU : IsDihedralRot U R) (hnil : IsTwoNil K R)
    (hKW : K ≤ normalizer (W : Set G)) (hW2 : IsPGroup 2 W)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hUW : U ≤ W) {k : G} (hk : k ∈ K) :
    k ∈ centralizer (W : Set G) ∨
      ∃ c ∈ centralizer (W : Set G), ∃ r ∈ R, r ∉ U ∧ k = c * r := by
  obtain ⟨o, ho, r, hr, rfl⟩ := hnil k hk
  have hoW : o ∈ normalizer (W : Set G) := by
    have : o = o * r * r⁻¹ := by group
    rw [this]
    exact mul_mem (hKW hk) (inv_mem (hKW (hR.le hr)))
  have hoC : o ∈ centralizer (W : Set G) := oddCoreIn_normalizer_le_centralizer hW2
    (oddCoreIn_inf_normalizer_le hΩ hK hR hU hW2 hUW (mem_inf.mpr ⟨ho, hoW⟩))
  by_cases hrU : r ∈ U
  · left
    exact mul_mem hoC (mem_centralizer_iff.mpr fun b hb => hWab b hb r (hUW hrU))
  · exact Or.inr ⟨o, hoC, r, hr, hrU, rfl⟩

theorem relIndex_centralizer_eq_two (hΩ : Assumption41 Ω) {K R U W : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylowOf 2 R K) (hU : IsDihedralRot U R) (hnil : IsTwoNil K R)
    (hKW : K ≤ normalizer (W : Set G)) (hW2 : IsPGroup 2 W)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hUW : U ≤ W) :
    (centralizer (W : Set G)).relIndex K = 2 := by
  obtain ⟨r, hrR, hrU⟩ := hU.exists_not_mem
  have hrC := not_mem_centralizer hU hUW hrR hrU
  have hWC : W ≤ centralizer (W : Set G) := fun a ha =>
    mem_centralizer_iff.mpr fun b hb => hWab b hb a ha
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨r, hR.le hrR⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rcases mem_centralizer_or hΩ hK hR hU hnil hKW hW2 hWab hUW b.2 with
    hb | ⟨c, hc, r', hr', hr'U, hbeq⟩
  · refine Or.inr ⟨hb, fun h => hrC ?_⟩
    have : r = (b : G)⁻¹ * ((b : G) * r) := by group
    rw [this]
    exact mul_mem (inv_mem hb) h
  · refine Or.inl ⟨?_, fun h => not_mem_centralizer hU hUW hr' hr'U ?_⟩
    · rw [hbeq, mul_assoc]
      exact mul_mem hc (hWC (hUW (hU.mul_mem_of_not_mem hr' hrR hr'U hrU)))
    · have : r' = c⁻¹ * b := by rw [hbeq]; group
      rw [this]
      exact mul_mem (inv_mem hc) h

omit [Finite G] in
theorem pow_mul_mem_iff {N : Subgroup G} [N.Normal] {c : G} (hc : c ∈ N) (x : G) (n : ℕ) :
    (c * x) ^ n ∈ N ↔ x ^ n ∈ N := by
  have hc1 : (QuotientGroup.mk' N) c = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hc
  have h : (QuotientGroup.mk' N) ((c * x) ^ n) = (QuotientGroup.mk' N) (x ^ n) := by
    rw [map_pow, map_pow, map_mul, hc1, one_mul]
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, MonoidHom.mem_ker, h]

theorem pow_mem_centralizer_of_normal (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω)
    {K J R T U V W : Subgroup G} [W.Normal] (hK : K ∈ Ω) (hJ : J ∈ Ω) (hR : IsSylowOf 2 R K)
    (hT : IsSylowOf 2 T J) (hU : IsDihedralRot U R) (hV : IsDihedralRot V T)
    (hnilK : IsTwoNil K R) (hnilJ : IsTwoNil J T) (hW2 : IsPGroup 2 W)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hUW : U ≤ W) (hVW : V ≤ W) {k j : G} (hk : k ∈ K)
    (hj : j ∈ J) (hkC : k ∉ centralizer (W : Set G)) (hjC : j ∉ centralizer (W : Set G)) :
    (k * j) ^ 2 ∈ centralizer (W : Set G) ∨ (k * j) ^ 3 ∈ centralizer (W : Set G) := by
  have hN : ∀ H : Subgroup G, H ≤ normalizer (W : Set G) := fun H =>
    le_top.trans (normalizer_eq_top_iff.mpr inferInstance).ge
  obtain ⟨c₁, hc₁, r, hrR, hrU, rfl⟩ :=
    (mem_centralizer_or hΩ hK hR hU hnilK (hN K) hW2 hWab hUW hk).resolve_left hkC
  obtain ⟨c₂, hc₂, s, hsT, hsV, rfl⟩ :=
    (mem_centralizer_or hΩ hJ hT hV hnilJ (hN J) hW2 hWab hVW hj).resolve_left hjC
  have hc : c₁ * (r * c₂ * r⁻¹) ∈ centralizer (W : Set G) :=
    mul_mem hc₁ (conj_mem_centralizer (hN R hrR) hc₂)
  have heq : c₁ * r * (c₂ * s) = c₁ * (r * c₂ * r⁻¹) * (r * s) := by group
  rw [heq, pow_mul_mem_iff hc, pow_mul_mem_iff hc]
  have hrr : r * r = 1 := hU.mul_self r hrR hrU
  have hss : s * s = 1 := hV.mul_self s hsT hsV
  by_cases hKJ : K = J
  · subst hKJ
    left
    rcases mem_centralizer_or hΩ hK hR hU hnilK (hN K) hW2 hWab hUW (hT.le hsT) with
      hs | ⟨c, hc', r', hr', hr'U, hseq⟩
    · exact absurd hs (not_mem_centralizer hV hVW hsT hsV)
    · have hrr' : r * r' ∈ centralizer (W : Set G) :=
        mem_centralizer_iff.mpr fun b hb =>
          hWab b hb _ (hUW (hU.mul_mem_of_not_mem hrR hr' hrU hr'U))
      have h1 : r * s = (r * c * r⁻¹) * (r * r') := by rw [hseq]; group
      rw [h1, pow_mul_mem_iff (conj_mem_centralizer (hN R hrR) hc')]
      exact pow_mem hrr' 2
  by_cases hA : T ≤ normalizer (K : Set G)
  · left
    obtain ⟨hJK, hKJ'⟩ := le_normalizer_of_sylow h22 hΩ hK hJ hKJ hT hA
    have h1 := commutator_mem_centralizer hΩ hK hJ hKJ hR hU hW2 hUW hJK hKJ' (hR.le hrR)
      (hT.le hsT) (hN R hrR) (hN T hsT)
    have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    rw [hrinv, hsinv] at h1
    rwa [pow_two, show r * s * (r * s) = r * s * r * s by group]
  · right
    exact pow_three_mem_centralizer h22 hΩ hK hJ hKJ hR hT hU hV hnilK hnilJ (hN R) (hN T) hW2
      hWab hUW hVW hA hrR hrU hsT hsV

theorem conclusion2_of_normal (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hnil : ∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R)
    (hW : (sec4W Ω S).Normal) :
    (sec4W Ω S).Normal ∧ (∀ K ∈ Ω, (centralizer (sec4W Ω S : Set G)).relIndex K = 2) ∧
      ∀ K ∈ Ω, ∀ J ∈ Ω, ∀ k ∈ K, ∀ j ∈ J, k ∉ centralizer (sec4W Ω S : Set G) →
        j ∉ centralizer (sec4W Ω S : Set G) →
        (k * j) ^ 2 ∈ centralizer (sec4W Ω S : Set G) ∨
          (k * j) ^ 3 ∈ centralizer (sec4W Ω S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := sec4W Ω S
  have hW2 : IsPGroup 2 W := hS.isPGroup.to_le (sec4W_le S)
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((isMulCommutative_sec4W hΩ hS.isPGroup).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hN : ∀ H : Subgroup G, H ≤ normalizer (W : Set G) := fun H =>
    le_top.trans (normalizer_eq_top_iff.mpr hW).ge
  have hsyl : ∀ K ∈ Ω, ∃ R U : Subgroup G, IsSylowOf 2 R K ∧ IsDihedralRot U R ∧ U ≤ W := by
    intro K hK
    obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
    obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
    exact ⟨R, U, hR, hU, rot_le_sec4W hΩ hS hK hR hU (hN R)⟩
  refine ⟨hW, fun K hK => ?_, fun K hK J hJ k hk j hj hkC hjC => ?_⟩
  · obtain ⟨R, U, hR, hU, hUW⟩ := hsyl K hK
    exact relIndex_centralizer_eq_two hΩ hK hR hU (hnil K hK R hR) (hN K) hW2 hWab hUW
  · obtain ⟨R, U, hR, hU, hUW⟩ := hsyl K hK
    obtain ⟨T, V, hT, hV, hVW⟩ := hsyl J hJ
    exact pow_mem_centralizer_of_normal h22 hΩ hK hJ hR hT hU hV (hnil K hK R hR)
      (hnil J hJ T hT) hW2 hWab hUW hVW hk hj hkC hjC

end CFSG.ComponentClassification.Asc76.Sec4
