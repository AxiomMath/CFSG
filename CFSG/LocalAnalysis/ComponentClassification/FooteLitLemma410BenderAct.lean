module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410Sylow
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderHypII
public import CFSG.Walter.W67.W2Cor32A

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools GSThmB
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem card_le_two_mul_of_forall_mem [Finite G] {E F : Subgroup G} (hFE : F ≤ E)
    (hsq : ∀ x ∈ E, x * x = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (h : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ∈ F ∨ e₂ ∈ F ∨ e₁ * e₂ ∈ F) :
    Nat.card E ≤ 2 * Nat.card F := by
  by_contra hlt
  push Not at hlt
  obtain ⟨e₁, he₁E, he₁F⟩ : ∃ e₁ ∈ E, e₁ ∉ F := by
    by_contra hall
    push Not at hall
    have := card_le_of_le (show E ≤ F from hall)
    omega
  set Z := zpowers e₁ with hZ
  have hZN : Z ≤ normalizer (F : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcomm e₁ he₁E y (hFE hy), mul_inv_cancel_right]
      exact hy
    · intro hy
      have hyE : y ∈ E := by
        have := E.mul_mem (E.mul_mem (E.inv_mem he₁E) (hFE hy)) he₁E
        simpa [mul_assoc] using this
      rwa [hcomm e₁ he₁E y hyE, mul_inv_cancel_right] at hy
  have hFZ : F ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxF, hxZ⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hxZ
    rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [mem_bot, ← two_mul, zpow_mul, show e₁ ^ (2 : ℤ) = 1 by
        rw [zpow_two, hsq e₁ he₁E], one_zpow]
    · exfalso
      apply he₁F
      have h1 : e₁ ^ (2 * k + 1) = e₁ := by
        rw [zpow_add, zpow_mul, show e₁ ^ (2 : ℤ) = 1 by rw [zpow_two, hsq e₁ he₁E], one_zpow,
          one_mul, zpow_one]
      rw [h1] at hxF
      exact hxF
  have hZcard : Nat.card Z = 2 := by
    rw [hZ, Nat.card_zpowers]
    refine orderOf_eq_prime (by rw [sq]; exact hsq e₁ he₁E) ?_
    intro h1
    apply he₁F
    rw [h1]
    exact F.one_mem
  have hFZcard : Nat.card (F ⊔ Z : Subgroup G) = 2 * Nat.card F := by
    have h := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hZN
    rw [hFZ, card_bot, mul_one, hZcard, mul_comm] at h
    exact h
  obtain ⟨e₂, he₂E, he₂FZ⟩ : ∃ e₂ ∈ E, e₂ ∉ F ⊔ Z := by
    by_contra hall
    push Not at hall
    have := card_le_of_le (show E ≤ F ⊔ Z from hall)
    omega
  have he₂F : e₂ ∉ F := fun h => he₂FZ (mem_sup_left h)
  have he₁₂F : e₁ * e₂ ∉ F := by
    intro h
    apply he₂FZ
    have : e₂ = e₁ * (e₁ * e₂) := by rw [← mul_assoc, hsq e₁ he₁E, one_mul]
    rw [this, sup_comm]
    exact mul_mem_sup (mem_zpowers e₁) h
  rcases h e₁ he₁E e₂ he₂E with h1 | h1 | h1
  · exact he₁F h1
  · exact he₂F h1
  · exact he₁₂F h1

omit [Finite G] in
theorem eq_one_of_mk_eq_one_of_isPGroup [Finite G] {K : Subgroup G} {Q : Subgroup ↥K}
    (hQ : IsPGroup 2 Q) {a : ↥K} (ha : a ∈ Q)
    (h1 : QuotientGroup.mk' (pPrimeCore 2 ↥K) a = 1) : a = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨k, hk⟩ := hQ ⟨a, ha⟩
  have h2 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    have := congrArg Subtype.val hk
    simpa using this)
  have h3 : orderOf a ∣ Nat.card (pPrimeCore 2 ↥K) := Subgroup.orderOf_dvd_natCard _ h1
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (odd_card_pPrimeCore_two ↥K))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h3)

theorem commute_of_oddBarConj_eq_conj {K R : Subgroup G}
    (hRK : IsSylowOf 2 R K) (hBen : Open.fusionIsBenderGroup (K ⧸ pPrimeCore 2 K))
    {y : G} (hyK : y ∈ normalizer (K : Set G)) (hyR : y ∈ normalizer (R : Set G))
    (hy2 : y * y = 1) {s : K ⧸ pPrimeCore 2 K}
    (hs : oddBarConj K ⟨y, hyK⟩ = MulAut.conj s) {r : G} (hr : r ∈ R) : y * r * y⁻¹ = r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBD := AschbacherToolkit.BenderExt.benderData_of_isBenderGroup hBen
  have : IsSimpleGroup (K ⧸ pPrimeCore 2 K) := hBD.simple
  obtain ⟨q, k, hq4, hB⟩ := hBD.borel
  set ρ := QuotientGroup.mk' (pPrimeCore 2 K) with hρ
  obtain ⟨R₁, hR₁⟩ := hRK
  set Rsyl : Sylow 2 (K ⧸ pPrimeCore 2 K) :=
    R₁.mapSurjective (QuotientGroup.mk'_surjective _) with hRsyl
  set Rs : Subgroup (K ⧸ pPrimeCore 2 K) := (Rsyl : Subgroup (K ⧸ pPrimeCore 2 K)) with hRs
  have hRsc : Rs = (R₁ : Subgroup K).map ρ := Sylow.coe_mapSurjective _ _
  have hmemR : ∀ a : ↥K, a ∈ (R₁ : Subgroup K) ↔ (a : G) ∈ R := fun a => by
    rw [← hR₁]
    exact (mem_map_iff_mem K.subtype_injective).symm
  have hnc : ∃ a b : K ⧸ pPrimeCore 2 K, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    apply ((hB Rsyl).1).1
    rw [eq_top_iff]
    intro x _
    rw [mem_normalizer_iff]
    intro z
    rw [show x * z * x⁻¹ = z by rw [hab x z, mul_inv_cancel_right]]
  obtain ⟨-, hZ⟩ := open_isQuasisimple_of_isSimpleGroup hnc
  have hcinj := injective_mulAut_conj hZ
  have hact : ∀ (n : ↥(normalizer (K : Set G))) (a : ↥K),
      oddBarConj K n (ρ a) = ρ ⟨(n : G) * a * (n : G)⁻¹,
        (mem_normalizer_iff.mp n.2 a).mp a.2⟩ := fun n a => by
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, oddBarConj_apply_mk]
  have hmaps : ∀ (n : ↥(normalizer (K : Set G))), (n : G) ∈ normalizer (R : Set G) →
      ∀ z ∈ Rs, oddBarConj K n z ∈ Rs := by
    intro n hnR z hz
    rw [hRsc] at hz ⊢
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hz
    rw [hact]
    exact mem_map_of_mem ρ ((hmemR _).mpr ((mem_normalizer_iff.mp hnR a).mp ((hmemR a).mp ha)))
  set n : ↥(normalizer (K : Set G)) := ⟨y, hyK⟩ with hn
  have hn2 : n * n = 1 := Subtype.ext hy2
  have hs2 : s * s = 1 := hcinj (by rw [map_mul, ← hs, ← map_mul, hn2, map_one, map_one])
  have hsN : s ∈ normalizer (Rs : Set (K ⧸ pPrimeCore 2 K)) := by
    have h1 : ∀ z, s * z * s⁻¹ = oddBarConj K n z := fun z => by rw [hs, MulAut.conj_apply]
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [h1]
      exact hmaps n hyR z hz
    · intro hz
      have h2 := hmaps n hyR _ hz
      rw [← h1] at h2
      have h3 : s * (s * z * s⁻¹) * s⁻¹ = z := by
        calc s * (s * z * s⁻¹) * s⁻¹ = (s * s) * z * (s * s)⁻¹ := by group
          _ = z := by rw [hs2, one_mul, inv_one, mul_one]
      rwa [h3] at h2
  have hsR : s ∈ Rs := by
    have hp : IsPGroup 2 ↥(zpowers s ⊔ Rs) :=
      (isPGroup_two_zpowers_of_sq_eq_one (by rw [sq]; exact hs2)).to_sup_of_normal_right'
        Rsyl.isPGroup' (zpowers_le.mpr hsN)
    have h : zpowers s ⊔ Rs = Rs := Rsyl.is_maximal' hp le_sup_right
    rw [← h]
    exact mem_sup_left (mem_zpowers s)
  have hsZ : s ∈ sylowCenter Rs :=
    AschbacherToolkit.Goldschmidt.mem_sylowCenter_of_sq_eq_one hB (by omega) Rsyl hsR
      (by rw [sq]; exact hs2)
  rw [← hR₁] at hr
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  have hρa : ρ a ∈ Rs := hRsc ▸ mem_map_of_mem ρ ha
  have h1 : ρ ⟨y * a * y⁻¹, (mem_normalizer_iff.mp hyK a).mp a.2⟩ = ρ a := by
    rw [← hact n a, hs, MulAut.conj_apply, ← (mem_sylowCenter.mp hsZ).2 _ hρa,
      mul_inv_cancel_right]
  have hyaR : (⟨y * a * y⁻¹, (mem_normalizer_iff.mp hyK a).mp a.2⟩ : ↥K) ∈ (R₁ : Subgroup K) :=
    (hmemR _).mpr ((mem_normalizer_iff.mp hyR a).mp ((hmemR a).mp ha))
  have h2 := eq_one_of_mk_eq_one_of_isPGroup R₁.isPGroup' (mul_mem hyaR (inv_mem ha))
    (by rw [map_mul, map_inv, h1, mul_inv_cancel])
  rw [mul_inv_eq_one] at h2
  exact congrArg Subtype.val h2

theorem exists_isKleinFour_le_of_bender
    {K E : Subgroup G} (hBen : Open.fusionIsBenderGroup (K ⧸ pPrimeCore 2 K))
    (hEK : E ≤ normalizer (K : Set G)) (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8) :
    ∃ W : Subgroup G, IsKleinFour W ∧ W ≤ E ∧ ∀ w ∈ W, ∀ hw : w ∈ normalizer (K : Set G),
      ∃ s, oddBarConj K ⟨w, hw⟩ = MulAut.conj s := by
  classical
  set φ := oddBarConj K with hφ
  set I : Subgroup G := E ⊓ (((MulAut.conj : (K ⧸ pPrimeCore 2 K) →*
    MulAut (K ⧸ pPrimeCore 2 K)).range.comap φ).map (normalizer (K : Set G)).subtype) with hI
  have hmemI : ∀ e (he : e ∈ E), e ∈ I ↔ ∃ s, φ ⟨e, hEK he⟩ = MulAut.conj s := by
    intro e he
    constructor
    · rintro ⟨-, y, ⟨s, hs⟩, rfl⟩
      exact ⟨s, hs.symm⟩
    · rintro ⟨s, hs⟩
      exact ⟨he, ⟨e, hEK he⟩, ⟨s, hs.symm⟩, rfl⟩
  have hE4 := RankTwoBender.e4Inner_of_bender hBen
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hE2 x hx
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    commute_of_sq_eq_one hE2 hx hy
  have hIcond : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ∈ I ∨ e₂ ∈ I ∨ e₁ * e₂ ∈ I := by
    intro e₁ he₁ e₂ he₂
    set n₁ : ↥(normalizer (K : Set G)) := ⟨e₁, hEK he₁⟩ with hn₁
    set n₂ : ↥(normalizer (K : Set G)) := ⟨e₂, hEK he₂⟩ with hn₂
    have h₁ : n₁ * n₁ = 1 := Subtype.ext (hsq e₁ he₁)
    have h₂ : n₂ * n₂ = 1 := Subtype.ext (hsq e₂ he₂)
    have h₁₂ : n₁ * n₂ = n₂ * n₁ := Subtype.ext (hcomm e₁ he₁ e₂ he₂)
    rcases hE4 (φ n₁) (φ n₂) (by rw [← map_mul, h₁, map_one]) (by rw [← map_mul, h₂, map_one])
        (by rw [← map_mul, ← map_mul, h₁₂]) with ⟨y, hy⟩ | ⟨y, hy⟩ | ⟨y, hy⟩
    · exact Or.inl ((hmemI e₁ he₁).mpr ⟨y, hy⟩)
    · exact Or.inr (Or.inl ((hmemI e₂ he₂).mpr ⟨y, hy⟩))
    · refine Or.inr (Or.inr ((hmemI (e₁ * e₂) (mul_mem he₁ he₂)).mpr ⟨y, ?_⟩))
      have : (⟨e₁ * e₂, hEK (mul_mem he₁ he₂)⟩ : ↥(normalizer (K : Set G))) = n₁ * n₂ := rfl
      rw [this, map_mul, hy]
  have hI4 : 4 ≤ Nat.card I := by
    have := card_le_two_mul_of_forall_mem (E := E) (F := I) inf_le_left hsq hcomm hIcond
    rw [hE8] at this
    omega
  obtain ⟨W, hW, hWI⟩ := exists_isKleinFour_le (fun x hx => hE2 x (mem_inf.mp hx).1) hI4
  refine ⟨W, hW, hWI.trans inf_le_left, fun w hw hwK => ?_⟩
  exact (hmemI w (mem_inf.mp (hWI hw)).1).mp (hWI hw)

theorem exists_mem_coreActionKernel_of_card_four {K R E : Subgroup G}
    (hRK : IsSylowOf 2 R K) (hR4 : Nat.card R = 4)
    (hBen : Open.fusionIsBenderGroup (K ⧸ pPrimeCore 2 K)) (hEK : E ≤ normalizer (K : Set G))
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8)
    (hER : ∀ e ∈ E, ∀ r ∈ R, e * r = r * e) :
    ∃ x ∈ E, x ≠ 1 ∧ x ∈ coreActionKernel K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBD := AschbacherToolkit.BenderExt.benderData_of_isBenderGroup hBen
  set ρ := QuotientGroup.mk' (pPrimeCore 2 K) with hρ
  obtain ⟨R₁, hR₁⟩ := hRK
  set Rsyl : Sylow 2 (K ⧸ pPrimeCore 2 K) :=
    R₁.mapSurjective (QuotientGroup.mk'_surjective _) with hRsyl
  set Rs : Subgroup (K ⧸ pPrimeCore 2 K) := (Rsyl : Subgroup (K ⧸ pPrimeCore 2 K)) with hRs
  have hRsc : Rs = (R₁ : Subgroup K).map ρ := Sylow.coe_mapSurjective _ _
  have hmemR : ∀ a : ↥K, a ∈ (R₁ : Subgroup K) ↔ (a : G) ∈ R := fun a => by
    rw [← hR₁]
    exact (mem_map_iff_mem K.subtype_injective).symm
  have hinj : Function.Injective (ρ.comp (R₁ : Subgroup K).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    exact Subtype.ext (eq_one_of_mk_eq_one_of_isPGroup R₁.isPGroup' a.2 ha)
  have hRs4 : Nat.card Rs = 4 := by
    have hr : (ρ.comp (R₁ : Subgroup K).subtype).range = Rs := by
      rw [MonoidHom.range_comp, range_subtype, hRsc]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← hR4, ← hR₁,
      card_map_of_injective K.subtype_injective]
  have hall : ∀ e (he : e ∈ E), ∃ s ∈ Rs, oddBarConj K ⟨e, hEK he⟩ = MulAut.conj s := by
    intro e he
    set α := oddBarConj K ⟨e, hEK he⟩ with hα
    have hfix : ∀ z ∈ Rs, α z = z := by
      intro z hz
      rw [hRsc] at hz
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hz
      rw [hα, hρ, QuotientGroup.mk'_apply, oddBarConj_apply_mk]
      congr 1
      apply Subtype.ext
      show e * (a : G) * e⁻¹ = a
      rw [hER e he _ ((hmemR a).mp ha), mul_inv_cancel_right]
    have hα2 : α ^ 2 ^ 1 = 1 := by
      have h1 : (⟨e, hEK he⟩ : ↥(normalizer (K : Set G))) * ⟨e, hEK he⟩ = 1 :=
        Subtype.ext (by rw [Subgroup.coe_mul, ← sq]; exact hE2 e he)
      rw [pow_one, sq, hα, ← map_mul, h1, map_one]
    by_contra hno
    push Not at hno
    obtain ⟨-, -, t', ht'R, ht'⟩ := hBD.aut Rsyl α (fun s hs => by rw [hfix s hs]; exact hs)
      (fun z hz => hfix z (mem_sylowCenter.mp hz).1) ⟨1, hα2⟩ hno
    rw [hfix t' ht'R, inv_mul_cancel] at ht'
    exact ht' (sylowCenter Rs).one_mem
  choose c hcR hc using hall
  let f : ↥E → ↥Rs := fun e => ⟨c e e.2, hcR e e.2⟩
  have hf : ¬ Function.Injective f := by
    intro hinj'
    have := Nat.card_le_card_of_injective f hinj'
    rw [hRs4, hE8] at this
    omega
  rw [Function.not_injective_iff] at hf
  obtain ⟨e₁, e₂, hfe, hne⟩ := hf
  have hce : c e₁ e₁.2 = c e₂ e₂.2 := congrArg Subtype.val hfe
  have hmem : (e₁ : G) * (e₂ : G)⁻¹ ∈ E := mul_mem e₁.2 (inv_mem e₂.2)
  refine ⟨(e₁ : G) * (e₂ : G)⁻¹, hmem, fun h1 => hne (Subtype.ext (mul_inv_eq_one.mp h1)), ?_⟩
  have hx : oddBarConj K ⟨(e₁ : G) * (e₂ : G)⁻¹, hEK hmem⟩ = 1 := by
    have : (⟨(e₁ : G) * (e₂ : G)⁻¹, hEK hmem⟩ : ↥(normalizer (K : Set G))) =
        ⟨e₁, hEK e₁.2⟩ * (⟨e₂, hEK e₂.2⟩)⁻¹ := rfl
    rw [this, map_mul, map_inv, hc e₁ e₁.2, hc e₂ e₂.2, hce, mul_inv_cancel]
  exact mem_coreActionKernel_of_oddBarConj_eq_one hx

theorem Foote410Config.exists_mem_coreActionKernel_footeK
    (h : FooteSec4 G L) (h47 : FooteThm47Statement) (hST : GSThmB.SuzukiTausskyInput)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G}
    (hM : IsFooteM L M) {g : G} {E Q : Subgroup G} {t : G} (hc : Foote410Config M g E Q t)
    (htK : t ∉ footeK L t) :
    IsSylowOf 2 (Q ⊓ footeK L t) (footeK L t) ∧
      ∃ x ∈ E, x ≠ 1 ∧ x ∈ coreActionKernel (footeK L t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht2, htC, hCt⟩ := hc.ht
  obtain ⟨hBN, -, -, -⟩ := foote_lemma_4_9_core h h47 hST hM ht2 htC hCt
  obtain ⟨-, -, -, -, htype, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM ht2 htC hCt
  have hBen : Open.fusionIsBenderGroup (footeK L t ⧸ pPrimeCore 2 (footeK L t)) := by
    rcases htype with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact h1
    · exact absurd h1 htK
  obtain ⟨T, hT, hQT, -, hRK, hER, hQR⟩ := hc.exists_sylow h h47 hST hAsc h2An hM
  set K := footeK L t with hK
  set R := T ⊓ K with hR
  have hEt : E ≤ centralizer ({t} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr (hc.hEQ e he t hc.htQ)
  have hEK : E ≤ normalizer (K : Set G) := fun e he => mem_normalizer_footeK (hBN (hEt he))
  obtain ⟨W, hW, hWE, hWinn⟩ := exists_isKleinFour_le_of_bender hBen hEK hc.hE2 hc.hE8
  have hWR : ∀ w ∈ W, ∀ r ∈ R, w * r * w⁻¹ = r := by
    intro w hw r hr
    obtain ⟨s, hs⟩ := hWinn w hw (hEK (hWE hw))
    exact commute_of_oddBarConj_eq_conj hRK hBen (hEK (hWE hw)) (hER (hWE hw))
      (by rw [← sq]; exact hc.hE2 w (hWE hw)) hs hr
  have hRN : R ≤ normalizer (conjugate M g : Set G) := fun r hr =>
    foote_cor_4_8_iv h h47 hST (isFooteM_conjugate h hM g) (hWE.trans hc.hEC) hW le_rfl
      (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw => by
        have h1 := hWR w hw r hr
        calc w * r = w * r * w⁻¹ * w := by group
          _ = r * w := by rw [h1]))
  have hRC : R ≤ coreActionKernel M := inf_le_left.trans (hT.le.trans inf_le_left)
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [hc.hQ8]; norm_num)
  have hQRp : IsPGroup 2 ↥(Q ⊔ R) := hQp.to_sup_of_normal_right' hRK.isPGroup hQR
  have hQR' := hc.hQSyl.eq_of_le (le_sup_left : Q ≤ Q ⊔ R)
    (sup_le hc.hQSyl.le (le_inf hRC hRN)) hQRp
  have hRQ : R ≤ Q := hQR' ▸ le_sup_right
  have hRV : R = Q ⊓ K := le_antisymm (le_inf hRQ inf_le_right) (inf_le_inf_right K hQT)
  have hV4 := hc.card_inf_footeK h h47 hST hAsc h2An hM htK
  have hRK' : IsSylowOf 2 (Q ⊓ K) K := hRV ▸ hRK
  exact ⟨hRK', exists_mem_coreActionKernel_of_card_four hRK' hV4 hBen hEK hc.hE2 hc.hE8
    fun e he r hr => hc.hEQ e he r (mem_inf.mp hr).1⟩

end CFSG.ComponentClassification.FooteLit
