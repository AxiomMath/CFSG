module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseDCover

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AS76b.Sec5

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

namespace Sec3

variable {R T : Subgroup G} {g : G}

section Config

variable (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) (D : ClassicalModel A)
  (hfam : D.family = .symplectic) (hq : 4 ≤ D.q)
include I hTy hfam hq

theorem exists_case23Setup_swap (hc : Sec3 A R T g) {p : G} {U W : Subgroup G} {y₁ y₂ : G}
    {ℓ : ℕ} (hS : Case23Setup D R T p U W y₁ y₂ ℓ) :
    ∃ (p₁ : G) (U₁ W₁ : Subgroup G) (z₁ z₂ : G) (ℓ₁ : ℕ),
      Case23Setup D (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p₁ U₁ W₁ z₁ z₂ ℓ₁ := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  have hZ := hS.oddCenter
  have hsw := hc.swap
  obtain ⟨t₁, ht₁, ht₁1⟩ := (rightConjugate R g⁻¹).bot_or_exists_ne_one.resolve_left
    hsw.T_ne_bot
  obtain ⟨p₁, hp₁, hρ₁⟩ := hsw.exists_aPart I.h32 I.h4 I.h34 ht₁
  have hcardV := hS.card_inf_sec3V hc I.h32 I.h4 I.h34
  rcases hsw.case222 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy I.h222 D hq ht₁ ht₁1 hp₁ hρ₁ with
    ⟨hle₁, -, hI₁⟩ | hII
  · have hsyl₁ := I.hJS.jSylowAt D hc.hyp.standard.1 hZ hq hp₁
      (hsw.orderOf_aPart I.h32 ht₁ ht₁1 hρ₁)
    rcases hI₁ with h1 | h23 | h4'
    · exfalso
      have h2 := hsw.card_inf_of_case14 I.h32 I.h4 I.h34 D hq ht₁ ht₁1 hp₁ hρ₁ hle₁
        (Or.inl h1) hsyl₁
      rw [hc.card_inf_sec3V_swap I.h32 I.h4 I.h34 hZ, hcardV] at h2
      nlinarith
    · obtain ⟨U₁, W₁, z₁, z₂, ℓ₁, hS₁⟩ :=
        hsw.exists_case23Setup I hTy D hfam hq ht₁ ht₁1 hp₁ hρ₁ h23
      exact ⟨p₁, U₁, W₁, z₁, z₂, ℓ₁, hS₁⟩
    · exfalso
      have h2 := hsw.card_inf_of_case14 I.h32 I.h4 I.h34 D hq ht₁ ht₁1 hp₁ hρ₁ hle₁
        (Or.inr h4') hsyl₁
      rw [hc.card_inf_sec3V_swap I.h32 I.h4 I.h34 hZ, hcardV] at h2
      nlinarith
  · exfalso
    have := hII.2.2
    omega

theorem exists_generic_or_eq (hc : Sec3 A R T g) (h117 : ClassicalPrimaryPerfect)
    (hAP : SymplecticTypeAPerfect) {p : G} {U W : Subgroup G} {y₁ y₂ : G} {ℓ : ℕ}
    (hS : Case23Setup D R T p U W y₁ y₂ ℓ) :
    (∃ x ∈ normalizer (sec3V R T : Set G), rightConjugate R x ≠ R ∧
      rightConjugate R x ⊓ (R ⊔ U) = ⊥ ∧ rightConjugate R x ⊓ (R ⊔ W) = ⊥) ∨
    sec3V R T ⊓ rightConjugate A g = sec3V R T ⊓ A := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hgen, hneq⟩ := hcon
  have hZ := hS.oddCenter
  have hJV := hS.jGroup_le_sec3V hc I.h32 I.h4 I.h34
  have hJA : jGroup A p ≤ A := hS.vdata.le
  have htwo := Case23Setup.two hc I.h32
  have hUW : ∀ x ∈ normalizer (sec3V R T : Set G),
      rightConjugate R x ≤ R ⊔ U ∨ rightConjugate R x ≤ R ⊔ W := by
    intro x hx
    by_cases hxR : rightConjugate R x = R
    · rw [hxR]
      exact Or.inl le_sup_left
    have h' := hc.of_mem_normalizer I.h32 hx hxR
    have hT'V := Lemma36.rightConjugate_le hc.R_le_sec3V hx
    rcases hS.trichotomy hc I hTy h' hT'V with hU' | hW' | hΓ
    · exact Or.inl (h'.le_sup_of_aParts I.h32 I.h4 I.h34 hU')
    · exact Or.inr (h'.le_sup_of_aParts I.h32 I.h4 I.h34 hW')
    · exact absurd (h'.inf_sup_eq_bot_of_aParts I.h32 I.h4 I.h34 hZ htwo hc.R_le_sec3V
        (hS.diag.W_le.trans hJV) (hS.diag.W_le.trans hJA)
        (fun s hs hs1 p' hp' hρ' => (hΓ s hs hs1 p' hp' hρ').2))
        (hgen x hx hxR (h'.inf_sup_eq_bot_of_aParts I.h32 I.h4 I.h34 hZ htwo hc.R_le_sec3V
        (hS.diag.U_le.trans hJV) (hS.diag.U_le.trans hJA)
        (fun s hs hs1 p' hp' hρ' => (hΓ s hs hs1 p' hp' hρ').1)))
  have hsw := hc.swap
  obtain ⟨w₀, hw₀⟩ := hc.exists_conj
  obtain ⟨p₁, U₁, W₁, z₁, z₂, ℓ₁, hS₁⟩ := hc.exists_case23Setup_swap I hTy D hfam hq hS
  have hV₁ : sec3V (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) =
      rightConjugate (sec3V R T) g⁻¹ := by
    rw [sec3V_rightConjugate, sec3V_symm hw₀]
  have hVeq₁ := hS₁.sec3V_eq_sup hsw I.h32 I.h4 I.h34
  have hzN : ∀ a ∈ (zpowers z₁ : Set G) ∪ zpowers z₂,
      g⁻¹ * a * g ∈ normalizer (sec3V R T : Set G) := by
    have hN₁ : ∀ a ∈ A ⊓ normalizer (jGroup A p₁ : Set G),
        a ∈ normalizer (sec3V (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) : Set G) := by
      intro a ha
      rw [hVeq₁]
      refine mem_normalizer_sup (centralizer_le_normalizer _ ?_) (mem_inf.mp ha).2
      rw [mem_centralizer_iff]
      intro r hr
      exact (mem_centralizer_iff.mp (hsw.sylowR.le hr) a (mem_inf.mp ha).1).symm
    intro a ha
    have haN : a ∈ A ⊓ normalizer (jGroup A p₁ : Set G) := by
      rcases ha with ha | ha
      · exact (zpowers_le.mpr hS₁.diag.y₁_mem) ha
      · exact (zpowers_le.mpr hS₁.diag.y₂_mem) ha
    have h1 := hN₁ a haN
    rw [hV₁, mem_normalizer_rightConjugate_iff] at h1
    simpa using h1
  have hconj : ∀ a : G, rightConjugate (rightConjugate R g⁻¹) a =
      rightConjugate (rightConjugate R (g⁻¹ * a * g)) g⁻¹ := by
    intro a
    rw [rightConjugate_mul, rightConjugate_mul, show g⁻¹ * a * g * g⁻¹ = g⁻¹ * a by group]
  have hT₁QU : rightConjugate R g⁻¹ ≤ rightConjugate (R ⊔ U) g⁻¹ := map_mono le_sup_left
  have hT₁QW : rightConjugate R g⁻¹ ≤ rightConjugate (R ⊔ W) g⁻¹ := map_mono le_sup_left
  have hQ : ∀ a ∈ (zpowers z₁ : Set G) ∪ zpowers z₂,
      rightConjugate (rightConjugate R g⁻¹) a ≤ rightConjugate (R ⊔ U) g⁻¹ ∨
        rightConjugate (rightConjugate R g⁻¹) a ≤ rightConjugate (R ⊔ W) g⁻¹ := by
    intro a ha
    rw [hconj]
    rcases hUW _ (hzN a ha) with h | h
    · exact Or.inl (map_mono h)
    · exact Or.inr (map_mono h)
  have hmemc : ∀ t ∈ rightConjugate R g⁻¹, ∀ a : G,
      a⁻¹ * t * a ∈ rightConjugate (rightConjugate R g⁻¹) a := by
    intro t ht a
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using ht
  have hidU : ∀ t ∈ rightConjugate R g⁻¹, ∀ τ ∈ rightConjugate T g⁻¹, ∀ u ∈ U₁, ∀ w ∈ W₁,
      t = τ * u * w → ∀ a ∈ zpowers z₂, u⁻¹ * (a⁻¹ * u * a) = t⁻¹ * (a⁻¹ * t * a) := by
    intro t _ τ hτ u hu w hw he a ha
    have haN : a ∈ A ⊓ normalizer (jGroup A p₁ : Set G) := (zpowers_le.mpr hS₁.diag.y₂_mem) ha
    have haA : a ∈ A := (mem_inf.mp haN).1
    have haW : a ∈ centralizer (W₁ : Set G) := (zpowers_le.mpr hS₁.diag.y₂_cent) ha
    have hua : a⁻¹ * u * a ∈ U₁ := by
      have := (mem_normalizer_iff.mp (inv_mem (hS₁.diag.normalizer_le_U haN)) u).mp hu
      simpa using this
    have h1 : a⁻¹ * τ * a = τ := by
      have := (hsw.commute_of_mem haA hτ).eq
      calc a⁻¹ * τ * a = a⁻¹ * (τ * a) := by group
        _ = a⁻¹ * (a * τ) := by rw [this]
        _ = τ := by group
    have h2 : a⁻¹ * w * a = w := by
      have := mem_centralizer_iff.mp haW w hw
      calc a⁻¹ * w * a = a⁻¹ * (w * a) := by group
        _ = a⁻¹ * (a * w) := by rw [this]
        _ = w := by group
    have h3 : w * (u⁻¹ * (a⁻¹ * u * a)) = (u⁻¹ * (a⁻¹ * u * a)) * w :=
      (hS₁.commute_U_W hsw I.h32 I.h4 I.h34 (mul_mem (inv_mem hu) hua) hw).symm
    calc u⁻¹ * (a⁻¹ * u * a) = w⁻¹ * (w * (u⁻¹ * (a⁻¹ * u * a))) := by group
      _ = w⁻¹ * ((u⁻¹ * (a⁻¹ * u * a)) * w) := by rw [h3]
      _ = (τ * u * w)⁻¹ * ((a⁻¹ * τ * a) * (a⁻¹ * u * a) * (a⁻¹ * w * a)) := by
        rw [h1, h2]; group
      _ = t⁻¹ * (a⁻¹ * t * a) := by rw [he]; group
  have hidW : ∀ t ∈ rightConjugate R g⁻¹, ∀ τ ∈ rightConjugate T g⁻¹, ∀ u ∈ U₁, ∀ w ∈ W₁,
      t = τ * u * w → ∀ a ∈ zpowers z₁, w⁻¹ * (a⁻¹ * w * a) = t⁻¹ * (a⁻¹ * t * a) := by
    intro t _ τ hτ u hu w _ he a ha
    have haN : a ∈ A ⊓ normalizer (jGroup A p₁ : Set G) := (zpowers_le.mpr hS₁.diag.y₁_mem) ha
    have haA : a ∈ A := (mem_inf.mp haN).1
    have haU : a ∈ centralizer (U₁ : Set G) := (zpowers_le.mpr hS₁.diag.y₁_cent) ha
    have h1 : a⁻¹ * τ * a = τ := by
      have := (hsw.commute_of_mem haA hτ).eq
      calc a⁻¹ * τ * a = a⁻¹ * (τ * a) := by group
        _ = a⁻¹ * (a * τ) := by rw [this]
        _ = τ := by group
    have h2 : a⁻¹ * u * a = u := by
      have := mem_centralizer_iff.mp haU u hu
      calc a⁻¹ * u * a = a⁻¹ * (u * a) := by group
        _ = a⁻¹ * (a * u) := by rw [this]
        _ = u := by group
    calc w⁻¹ * (a⁻¹ * w * a) =
        (τ * u * w)⁻¹ * ((a⁻¹ * τ * a) * (a⁻¹ * u * a) * (a⁻¹ * w * a)) := by
          rw [h1, h2]; group
      _ = t⁻¹ * (a⁻¹ * t * a) := by rw [he]; group
  have hδU : ∀ t ∈ rightConjugate R g⁻¹, ∀ τ ∈ rightConjugate T g⁻¹, ∀ u ∈ U₁, ∀ w ∈ W₁,
      t = τ * u * w → ∀ a ∈ zpowers z₂, u⁻¹ * (a⁻¹ * u * a) ∈ rightConjugate (R ⊔ U) g⁻¹ ∨
        u⁻¹ * (a⁻¹ * u * a) ∈ rightConjugate (R ⊔ W) g⁻¹ := by
    intro t ht τ hτ u hu w hw he a ha
    rw [hidU t ht τ hτ u hu w hw he a ha]
    rcases hQ a (Or.inr ha) with h | h
    · exact Or.inl (mul_mem (inv_mem (hT₁QU ht)) (h (hmemc t ht a)))
    · exact Or.inr (mul_mem (inv_mem (hT₁QW ht)) (h (hmemc t ht a)))
  have hδW : ∀ t ∈ rightConjugate R g⁻¹, ∀ τ ∈ rightConjugate T g⁻¹, ∀ u ∈ U₁, ∀ w ∈ W₁,
      t = τ * u * w → ∀ a ∈ zpowers z₁, w⁻¹ * (a⁻¹ * w * a) ∈ rightConjugate (R ⊔ U) g⁻¹ ∨
        w⁻¹ * (a⁻¹ * w * a) ∈ rightConjugate (R ⊔ W) g⁻¹ := by
    intro t ht τ hτ u hu w hw he a ha
    rw [hidW t ht τ hτ u hu w hw he a ha]
    rcases hQ a (Or.inl ha) with h | h
    · exact Or.inl (mul_mem (inv_mem (hT₁QU ht)) (h (hmemc t ht a)))
    · exact Or.inr (mul_mem (inv_mem (hT₁QW ht)) (h (hmemc t ht a)))
  obtain ⟨t, ht, ht1, t', ht', ht'1, htt⟩ := hsw.exists_ne_ne
  obtain ⟨τ, hτ, u, hu, hu1, w, hw, hw1, he⟩ := hS₁.exists_decomp hsw I.h32 I.h4 I.h34 ht ht1
  obtain ⟨τ', hτ', u', hu', hu'1, w', hw', hw'1, he'⟩ :=
    hS₁.exists_decomp hsw I.h32 I.h4 I.h34 ht' ht'1
  obtain ⟨huu, hww⟩ :=
    hS₁.ne_of_decomp hsw I.h32 I.h4 I.h34 ht ht' htt hτ hτ' hu hu' hw hw' he he'
  have hU₁ : U₁ ≤ rightConjugate (R ⊔ U) g⁻¹ ∨ U₁ ≤ rightConjugate (R ⊔ W) g⁻¹ := by
    apply le_or_le_of_forall_mem_or
    intro s hs
    by_cases hus : u * s = 1
    · have hu's : u' * s ≠ 1 := by
        intro h
        apply huu
        rw [eq_inv_of_mul_eq_one_left hus, eq_inv_of_mul_eq_one_left h]
      obtain ⟨a, ha, hav⟩ := hS₁.diag.trans_U hu' hu'1 (mul_mem hu' hs) hu's
      have h1 := hδU t' ht' τ' hτ' u' hu' w' hw' he' a ha
      rwa [hav, show u'⁻¹ * (u' * s) = s by group] at h1
    · obtain ⟨a, ha, hav⟩ := hS₁.diag.trans_U hu hu1 (mul_mem hu hs) hus
      have h1 := hδU t ht τ hτ u hu w hw he a ha
      rwa [hav, show u⁻¹ * (u * s) = s by group] at h1
  have hW₁ : W₁ ≤ rightConjugate (R ⊔ U) g⁻¹ ∨ W₁ ≤ rightConjugate (R ⊔ W) g⁻¹ := by
    apply le_or_le_of_forall_mem_or
    intro s hs
    by_cases hws : w * s = 1
    · have hw's : w' * s ≠ 1 := by
        intro h
        apply hww
        rw [eq_inv_of_mul_eq_one_left hws, eq_inv_of_mul_eq_one_left h]
      obtain ⟨a, ha, hav⟩ := hS₁.diag.trans_W hw' hw'1 (mul_mem hw' hs) hw's
      have h1 := hδW t' ht' τ' hτ' u' hu' w' hw' he' a ha
      rwa [hav, show w'⁻¹ * (w' * s) = s by group] at h1
    · obtain ⟨a, ha, hav⟩ := hS₁.diag.trans_W hw hw1 (mul_mem hw hs) hws
      have h1 := hδW t ht τ hτ u hu w hw he a ha
      rwa [hav, show w⁻¹ * (w * s) = s by group] at h1
  have hT₁inf := hS₁.T_inf_sup_U hsw I.h32 I.h4 I.h34
  have hT₁infW := hS₁.T_inf_sup_W hsw I.h32 I.h4 I.h34
  have hmemU : ∃ a ∈ zpowers z₂, rightConjugate R (g⁻¹ * a * g) ≠ R := by
    obtain ⟨v, hv, hv1, hvu⟩ := exists_ne_ne_of_three_le hS₁.diag.three_le_U 1 u
    obtain ⟨a, ha, hav⟩ := hS₁.diag.trans_U hu hu1 hv hv1
    refine ⟨a, ha, fun hR => hvu ?_⟩
    have hat : a⁻¹ * t * a ∈ rightConjugate R g⁻¹ := by
      have h1 := hmemc t ht a
      rwa [hconj, hR] at h1
    have h0 : u⁻¹ * v ∈ rightConjugate R g⁻¹ ⊓ (rightConjugate T g⁻¹ ⊔ U₁) := by
      refine mem_inf.mpr ⟨?_, mem_sup_right (mul_mem (inv_mem hu) hv)⟩
      rw [← hav, hidU t ht τ hτ u hu w hw he a ha]
      exact mul_mem (inv_mem ht) hat
    rw [hT₁inf, mem_bot] at h0
    exact (eq_of_inv_mul_eq_one h0).symm
  have hmemW : ∃ a ∈ zpowers z₁, rightConjugate R (g⁻¹ * a * g) ≠ R := by
    obtain ⟨v, hv, hv1, hvw⟩ := exists_ne_ne_of_three_le hS₁.diag.three_le_W 1 w
    obtain ⟨a, ha, hav⟩ := hS₁.diag.trans_W hw hw1 hv hv1
    refine ⟨a, ha, fun hR => hvw ?_⟩
    have hat : a⁻¹ * t * a ∈ rightConjugate R g⁻¹ := by
      have h1 := hmemc t ht a
      rwa [hconj, hR] at h1
    have h0 : w⁻¹ * v ∈ rightConjugate R g⁻¹ ⊓ (rightConjugate T g⁻¹ ⊔ W₁) := by
      refine mem_inf.mpr ⟨?_, mem_sup_right (mul_mem (inv_mem hw) hv)⟩
      rw [← hav, hidW t ht τ hτ u hu w hw he a ha]
      exact mul_mem (inv_mem ht) hat
    rw [hT₁infW, mem_bot] at h0
    exact (eq_of_inv_mul_eq_one h0).symm
  have hmem : ∀ Y : Subgroup G, (U₁ ≤ rightConjugate (R ⊔ Y) g⁻¹ ∨
      W₁ ≤ rightConjugate (R ⊔ Y) g⁻¹) → ∃ x ∈ normalizer (sec3V R T : Set G),
        rightConjugate R x ≠ R ∧ rightConjugate R x ≤ R ⊔ Y := by
    intro Y hY
    have hT₁Y : rightConjugate R g⁻¹ ≤ rightConjugate (R ⊔ Y) g⁻¹ := map_mono le_sup_left
    rcases hY with h | h
    · obtain ⟨a, ha, hne⟩ := hmemU
      refine ⟨_, hzN a (Or.inr ha), hne, ?_⟩
      have h1 := (hS₁.conj_le_sup_U hsw I.h32 I.h4 I.h34 ha).trans (sup_le hT₁Y h)
      rw [hconj] at h1
      exact rightConjugate_le_rightConjugate_iff.mp h1
    · obtain ⟨a, ha, hne⟩ := hmemW
      refine ⟨_, hzN a (Or.inl ha), hne, ?_⟩
      have h1 := (hS₁.conj_le_sup_W hsw I.h32 I.h4 I.h34 ha).trans (sup_le hT₁Y h)
      rw [hconj] at h1
      exact rightConjugate_le_rightConjugate_iff.mp h1
  have hcontra : ∀ z : G, rightConjugate R z ≤ sec3V R T → rightConjugate R z ≠ T →
      ∀ v ∈ rightConjugate R z, v ≠ 1 → g * v * g⁻¹ ∉ U₁ ∧ g * v * g⁻¹ ∉ W₁ := by
    intro z hzV hzT v hv hv1
    have hQe : rightConjugate (rightConjugate T g⁻¹) (g * w₀⁻¹ * z * g⁻¹) =
        rightConjugate (rightConjugate R z) g⁻¹ := by
      rw [hw₀, rightConjugate_mul, rightConjugate_mul, rightConjugate_mul]
      congr 1
      group
    have hQC : rightConjugate (rightConjugate T g⁻¹) (g * w₀⁻¹ * z * g⁻¹) ≤
        centralizer (rightConjugate T g⁻¹ : Set G) := by
      rw [hQe]
      have h1 : rightConjugate (rightConjugate R z) g⁻¹ ≤ rightConjugate (sec3V R T) g⁻¹ :=
        map_mono hzV
      refine h1.trans ?_
      rw [← hV₁]
      exact hsw.sec3V_le_centralizer_R I.h32
    have hQne : rightConjugate (rightConjugate T g⁻¹) (g * w₀⁻¹ * z * g⁻¹) ≠
        rightConjugate T g⁻¹ := by
      rw [hQe]
      intro h
      apply hzT
      have := congrArg (fun Q => rightConjugate Q g) h
      simpa only [rightConjugate_inv_rightConjugate] using this
    have h'' := hsw.of_le_centralizer hQC hQne
    have hgv : g * v * g⁻¹ ∈ rightConjugate (rightConjugate T g⁻¹) (g * w₀⁻¹ * z * g⁻¹) := by
      rw [hQe, mem_rightConjugate_iff, show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v by group]
      exact hv
    have hgv1 : g * v * g⁻¹ ≠ 1 := fun h => hv1 (by
      calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
    refine ⟨fun hU => ?_, fun hW => ?_⟩
    · obtain ⟨k, hk⟩ := hS₁.typeA_of_mem_U hU hgv1
      exact h''.false_of_mem_typeA I hTy D hfam hq hAP hgv hgv1 hk
    · exact h''.false_of_mem_primary I hTy D hq h117 hgv hgv1 (hS₁.prim_W _ hW hgv1)
  have hRUV : R ⊔ U ≤ sec3V R T := sup_le hc.R_le_sec3V (hS.diag.U_le.trans hJV)
  have hRWV : R ⊔ W ≤ sec3V R T := sup_le hc.R_le_sec3V (hS.diag.W_le.trans hJV)
  have hTU := hS.T_inf_sup_U hc I.h32 I.h4 I.h34
  have hTW := hS.T_inf_sup_W hc I.h32 I.h4 I.h34
  have hcov : ∀ (X₁ Y : Subgroup G), (X₁ = U₁ ∨ X₁ = W₁) → (Y = U ∨ Y = W) →
      X₁ ≤ rightConjugate (R ⊔ Y) g⁻¹ → rightConjugate X₁ g ≤ Y := by
    intro X₁ Y hX₁ hY hXQ v' hv'
    have hv'RY : v' ∈ R ⊔ Y := by
      have := (rightConjugate_le_rightConjugate_iff (x := g)).mpr hXQ hv'
      rwa [rightConjugate_inv_rightConjugate] at this
    obtain ⟨x, hx, hne, hle⟩ := hmem Y (by rcases hX₁ with rfl | rfl <;> simp [hXQ])
    by_contra hv'Y
    have hv'1 : v' ≠ 1 := fun h => hv'Y (h ▸ one_mem _)
    obtain ⟨z, hz, hv'z⟩ : ∃ z : G, rightConjugate R z ≤ R ⊔ Y ∧ v' ∈ rightConjugate R z := by
      rcases hY with rfl | rfl
      · exact hS.cover_U hc I hTy hfam hq hAP hx hne hle v' hv'RY hv'Y
      · exact hS.cover_W hc I hTy hfam hq h117 hx hne hle v' hv'RY hv'Y
    have hRYV : R ⊔ Y ≤ sec3V R T := by rcases hY with rfl | rfl <;> assumption
    have hzT : rightConjugate R z ≠ T := by
      intro h
      have h1 : v' ∈ T ⊓ (R ⊔ Y) := mem_inf.mpr ⟨h ▸ hv'z, hv'RY⟩
      rcases hY with rfl | rfl
      · rw [hTU, mem_bot] at h1
        exact hv'1 h1
      · rw [hTW, mem_bot] at h1
        exact hv'1 h1
    have hgv : g * v' * g⁻¹ ∈ X₁ := (mem_rightConjugate_iff _ _ _).mp hv'
    obtain ⟨hnU, hnW⟩ := hcontra z (hz.trans hRYV) hzT v' hv'z hv'1
    rcases hX₁ with rfl | rfl
    · exact hnU hgv
    · exact hnW hgv
  have hU' : rightConjugate U₁ g ≤ U ⊔ W := by
    rcases hU₁ with h | h
    · exact (hcov U₁ U (Or.inl rfl) (Or.inl rfl) h).trans le_sup_left
    · exact (hcov U₁ W (Or.inl rfl) (Or.inr rfl) h).trans le_sup_right
  have hW' : rightConjugate W₁ g ≤ U ⊔ W := by
    rcases hW₁ with h | h
    · exact (hcov W₁ U (Or.inr rfl) (Or.inl rfl) h).trans le_sup_left
    · exact (hcov W₁ W (Or.inr rfl) (Or.inr rfl) h).trans le_sup_right
  have hJ' : sec3V R T ⊓ rightConjugate A g ≤ sec3V R T ⊓ A := by
    have h2 : rightConjugate (jGroup A p₁) g = sec3V R T ⊓ rightConjugate A g := by
      rw [← hS₁.inf_sec3V_eq hsw I.h32 I.h4 I.h34, hV₁, rightConjugate_inf,
        rightConjugate_inv_rightConjugate]
    rw [← h2, hS₁.diag.J_eq, rightConjugate_sup, hS.inf_sec3V_eq hc I.h32 I.h4 I.h34,
      hS.diag.J_eq]
    exact sup_le hU' hW'
  have hcard : Nat.card ↥(sec3V R T ⊓ A) = Nat.card ↥(sec3V R T ⊓ rightConjugate A g) := by
    have h1 := hc.card_sec3V_eq I.h32 I.h4 I.h34 hZ
    have h2 := hc.card_sec3V_eq' I.h32 I.h4 I.h34 hZ
    rw [hc.card_eq] at h2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.symm.trans h2)
  exact hneq (eq_of_le_of_card_ge hJ' hcard.le)

theorem mem_gFused_iff (hc : Sec3 A R T g) (h117 : ClassicalPrimaryPerfect)
    (hAP : SymplecticTypeAPerfect) {p : G} {U W : Subgroup G} {y₁ y₂ : G} {ℓ : ℕ}
    (hS : Case23Setup D R T p U W y₁ y₂ ℓ)
    (hneq : sec3V R T ⊓ rightConjugate A g ≠ sec3V R T ⊓ A) {v : G} (hv : v ∈ sec3V R T) :
    v ∈ gFused (normalizer (sec3V R T : Set G)) R ↔ v ∉ A := by
  obtain ⟨x, hx, hne, hxU, hxW⟩ :=
    (hc.exists_generic_or_eq I hTy D hfam hq h117 hAP hS).resolve_right hneq
  have hU51 : ∀ x ∈ normalizer (sec3V R T : Set G), rightConjugate R x ≠ R →
      rightConjugate R x ≤ R ⊔ U → (rightConjugate R x = U ∧
        ∀ T'' ∈ gMembers (normalizer (sec3V R T : Set G)) R, T'' ≤ R ⊔ U →
          T'' = R ∨ T'' = U) ∨ rightConjugate R x ⊓ U = ⊥ := by
    intro x hx hne _
    right
    have h' := hc.of_mem_normalizer I.h32 hx hne
    rw [eq_bot_iff]
    intro u hu
    rw [mem_bot]
    by_contra hu1
    obtain ⟨huT, huU⟩ := mem_inf.mp hu
    obtain ⟨k, hk⟩ := hS.typeA_of_mem_U huU hu1
    exact h'.false_of_mem_typeA I hTy D hfam hq hAP huT hu1 hk
  have hW51 : ∀ x ∈ normalizer (sec3V R T : Set G), rightConjugate R x ≠ R →
      rightConjugate R x ≤ R ⊔ W → (rightConjugate R x = W ∧
        ∀ T'' ∈ gMembers (normalizer (sec3V R T : Set G)) R, T'' ≤ R ⊔ W →
          T'' = R ∨ T'' = W) ∨ rightConjugate R x ⊓ W = ⊥ := by
    intro x hx hne _
    right
    have h' := hc.of_mem_normalizer I.h32 hx hne
    rw [eq_bot_iff]
    intro w hw
    rw [mem_bot]
    by_contra hw1
    obtain ⟨hwT, hwW⟩ := mem_inf.mp hw
    exact h'.false_of_mem_primary I hTy D hq h117 hwT hw1 (hS.prim_W w hwW hw1)
  have hG := hS.gHyp51 hc I hTy hU51 hW51 ⟨rightConjugate R x, ⟨x, hx, rfl⟩, hne, hxU, hxW⟩
  have hiff : v ∈ U ⊔ W ↔ v ∈ A := by
    rw [← hS.diag.J_eq, ← hS.inf_sec3V_eq hc I.h32 I.h4 I.h34, mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  rcases fusionLemmaG_rot hG with ⟨hSig, -, -⟩ | ⟨-, -, -, x', hx', hWx⟩
  · rw [hSig]
    exact ⟨fun h hvA => h.2 (hiff.mpr hvA), fun hvA => ⟨hv, fun h => hvA (hiff.mp h)⟩⟩
  · exfalso
    obtain ⟨w, hw, hw1⟩ := W.bot_or_exists_ne_one.resolve_left (by
      intro h
      have := hS.card_W
      rw [h, card_bot] at this
      omega)
    have hne' : rightConjugate R x' ≠ R := by
      intro h
      have hwR : w ∈ R ⊓ A := mem_inf.mpr ⟨h ▸ hWx ▸ hw, hS.diag.W_le.trans hS.vdata.le hw⟩
      rw [hc.R_inf_A hS.oddCenter, mem_bot] at hwR
      exact hw1 hwR
    have h' := hc.of_mem_normalizer I.h32 hx' hne'
    exact h'.false_of_mem_primary I hTy D hq h117 (hWx ▸ hw) hw1 (hS.prim_W w hw hw1)

theorem false_of_case23_of_le (hc : Sec3 A R T g) (h117 : ClassicalPrimaryPerfect)
    (hAP : SymplecticTypeAPerfect) (hTA : T ≤ A) {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) (h23 : Case23 D p) : False := by
  obtain ⟨U, W, y₁, y₂, ℓ, hS⟩ := hc.exists_case23Setup I hTy D hfam hq ht ht1 hp hρ h23
  have hZ := hS.oddCenter
  have hneq : sec3V R T ⊓ rightConjugate A g ≠ sec3V R T ⊓ A := by
    intro h
    have htV : t ∈ sec3V R T ⊓ A := mem_inf.mpr ⟨hc.T_le_sec3V ht, hTA ht⟩
    rw [← h] at htV
    have h1 : t ∈ T ⊓ rightConjugate A g := mem_inf.mpr ⟨ht, (mem_inf.mp htV).2⟩
    rw [hc.T_inf_conj hZ, mem_bot] at h1
    exact ht1 h1
  have hsw := hc.swap
  obtain ⟨w₀, hw₀⟩ := hc.exists_conj
  obtain ⟨p₁, U₁, W₁, z₁, z₂, ℓ₁, hS₁⟩ := hc.exists_case23Setup_swap I hTy D hfam hq hS
  have hV₁ : sec3V (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) =
      rightConjugate (sec3V R T) g⁻¹ := by
    rw [sec3V_rightConjugate, sec3V_symm hw₀]
  have hneq₁ : sec3V (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) ⊓ rightConjugate A g⁻¹ ≠
      sec3V (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) ⊓ A := by
    rw [hV₁]
    intro h
    apply hneq
    have h' := congrArg (fun Q => rightConjugate Q g) h
    simp only [rightConjugate_inf, rightConjugate_inv_rightConjugate] at h'
    exact h'.symm
  have hkey : ∀ v ∈ sec3V R T, v ∉ rightConjugate A g → v ∈ A := by
    intro v hv hvA
    have hv₁ : g * v * g⁻¹ ∈ sec3V (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) := by
      rw [hV₁, mem_rightConjugate_iff, show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v by group]
      exact hv
    have hv₁A : g * v * g⁻¹ ∉ A := fun h => hvA ((mem_rightConjugate_iff _ _ _).mpr h)
    obtain ⟨a, ha, r₁, hr₁, hr₁1, hvr⟩ :=
      (hsw.mem_gFused_iff I hTy D hfam hq h117 hAP hS₁ hneq₁ hv₁).mpr hv₁A
    have hsT : g⁻¹ * r₁ * g ∈ T := by
      rw [mem_rightConjugate_iff, inv_inv] at hr₁
      exact hr₁
    have hxN : g⁻¹ * a * g ∈ normalizer (sec3V R T : Set G) := by
      rw [hV₁, mem_normalizer_rightConjugate_iff] at ha
      simpa using ha
    have hveq : v = (g⁻¹ * a * g)⁻¹ * (g⁻¹ * r₁ * g) * (g⁻¹ * a * g) := by
      calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
        _ = g⁻¹ * (a⁻¹ * r₁ * a) * g := by rw [hvr]
        _ = (g⁻¹ * a * g)⁻¹ * (g⁻¹ * r₁ * g) * (g⁻¹ * a * g) := by group
    by_contra hvA'
    obtain ⟨y, hy, r, hr, hr1, hyr⟩ :=
      (hc.mem_gFused_iff I hTy D hfam hq h117 hAP hS hneq hv).mpr hvA'
    have hsF : g⁻¹ * r₁ * g ∈ gFused (normalizer (sec3V R T : Set G)) R := by
      refine ⟨y * (g⁻¹ * a * g)⁻¹, mul_mem hy (inv_mem hxN), r, hr, hr1, ?_⟩
      calc (y * (g⁻¹ * a * g)⁻¹)⁻¹ * r * (y * (g⁻¹ * a * g)⁻¹) =
          (g⁻¹ * a * g) * (y⁻¹ * r * y) * (g⁻¹ * a * g)⁻¹ := by group
        _ = (g⁻¹ * a * g) * v * (g⁻¹ * a * g)⁻¹ := by rw [hyr]
        _ = g⁻¹ * r₁ * g := by rw [hveq]; group
    exact ((hc.mem_gFused_iff I hTy D hfam hq h117 hAP hS hneq (hc.T_le_sec3V hsT)).mp hsF)
      (hTA hsT)
  obtain ⟨r, hr, hr1⟩ := R.bot_or_exists_ne_one.resolve_left hc.R_ne_bot
  have hrA : r ∉ A := fun h => hr1 (by
    have h1 : r ∈ R ⊓ A := mem_inf.mpr ⟨hr, h⟩
    rwa [hc.R_inf_A hZ, mem_bot] at h1)
  have hrAg : r ∈ rightConjugate A g := by
    by_contra h
    exact hrA (hkey r (hc.R_le_sec3V hr) h)
  have htAg : t ∉ rightConjugate A g := fun h => ht1 (by
    have h1 : t ∈ T ⊓ rightConjugate A g := mem_inf.mpr ⟨ht, h⟩
    rwa [hc.T_inf_conj hZ, mem_bot] at h1)
  have hrtV : r * t ∈ sec3V R T := mul_mem (hc.R_le_sec3V hr) (hc.T_le_sec3V ht)
  by_cases hrt : r * t ∈ rightConjugate A g
  · exact htAg (by simpa using mul_mem (inv_mem hrAg) hrt)
  · exact hrA (by simpa using mul_mem (hkey _ hrtV hrt) (inv_mem (hTA ht)))

end Config

end Sec3

end CFSG.ComponentClassification.RankTwoClassical
