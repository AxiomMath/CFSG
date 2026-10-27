module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCoverSp
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplitSp

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AS76b.Sec5
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem le_or_le_of_forall_mem_or {S Q₁ Q₂ : Subgroup G} (h : ∀ s ∈ S, s ∈ Q₁ ∨ s ∈ Q₂) :
    S ≤ Q₁ ∨ S ≤ Q₂ := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  have hex : ∀ Q : Subgroup G, ¬ S ≤ Q → ∃ a ∈ S, a ∉ Q := by
    intro Q hQ
    by_contra hc
    push Not at hc
    exact hQ fun x hx => hc x hx
  obtain ⟨a, haS, haQ⟩ := hex Q₁ h1
  obtain ⟨b, hbS, hbQ⟩ := hex Q₂ h2
  have ha2 : a ∈ Q₂ := (h a haS).resolve_left haQ
  have hb1 : b ∈ Q₁ := (h b hbS).resolve_right hbQ
  rcases h (a * b) (mul_mem haS hbS) with hab | hab
  · exact haQ (by simpa using mul_mem hab (inv_mem hb1))
  · exact hbQ (by simpa using mul_mem (inv_mem ha2) hab)

namespace Sec3

variable {R T : Subgroup G} {g : G}

theorem false_of_mem_perfectCore (hc : Sec3 A R T g)
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZ : Odd (Nat.card (center A))) {t : G} (htT : t ∈ T) (ht1 : t ≠ 1)
    (hpc : t ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer ({t} : Set G))) : False := by
  have h2 : CFSG.Quasithin.perfectCore (A ⊓ centralizer ({t} : Set G)) ≤
      admResidual (oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
        ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆) :=
    le_admResidual_of_perfect
      ((CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans le_sup_right)
      (CFSG.Quasithin.perfectCore_perfect _)
  have htg : t ∈ rightConjugate A g :=
    (Lemma39.lemma39_one h4 h32 h34 hc.hyp hc.sylowT htT ht1 hOut).1 (h2 hpc)
  have h3 : t ∈ T ⊓ rightConjugate A g := mem_inf.mpr ⟨htT, htg⟩
  rw [hc.T_inf_conj hZ, mem_bot] at h3
  exact ht1 h3

section Config

variable (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) (D : ClassicalModel A)
  (hfam : D.family = .symplectic) (hq : 4 ≤ D.q)
include I hTy hfam hq

theorem false_of_mem_typeA (hc : Sec3 A R T g) (hAP : SymplecticTypeAPerfect) {t : G}
    (htT : t ∈ T) (ht1 : t ≠ 1) {k : ℕ} (htk : D.SuzukiType t .a k) : False := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  have hZ : Odd (Nat.card (center ↥A)) :=
    (I.h222.conclusion D hq (hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)).1
  exact hc.false_of_mem_perfectCore I.h4 I.h32 I.h34 hOut hZ htT ht1
    (hAP G A D hfam hc.hyp.standard.1 hZ hq t k htk)

omit hfam in
theorem false_of_mem_primary (hc : Sec3 A R T g) (h117 : ClassicalPrimaryPerfect) {t : G}
    (htT : t ∈ T) (ht1 : t ≠ 1) (htp : D.IsPrimary t) : False := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  have hZ : Odd (Nat.card (center ↥A)) :=
    (I.h222.conclusion D hq (hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)).1
  exact hc.false_of_mem_isPrimary I.h4 I.h32 I.h34 h117 D hq hOut hZ htT ht1 htp

omit hfam in
theorem case1_of_typeA (hc : Sec3 A R T g) {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A)
    (hρ : t⁻¹ * p ∈ R) {k : ℕ} (hpa : D.SuzukiType p .a k) : Case1 D p := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  rcases hc.case222 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy I.h222 D hq ht ht1 hp hρ with
    ⟨-, -, h1 | h23 | h4'⟩ | hII
  · exact h1
  · exfalso
    obtain ⟨ℓ, a, b, hcase, -⟩ := h23
    rcases hcase with ⟨-, hpb, -⟩ | ⟨hpc, -⟩
    · have := (D.suzukiType_unique hpa hpb).1
      cases this
    · have := (D.suzukiType_unique hpa hpc).1
      cases this
  · exfalso
    obtain ⟨⟨ℓ, hpc⟩, -⟩ := h4'
    have := (D.suzukiType_unique hpa hpc).1
    cases this
  · exfalso
    have := hII.2.2
    omega

omit hfam in
theorem case1_of_isPrimary (hc : Sec3 A R T g) {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) (hpp : D.IsPrimary p) :
    (∀ t' ∈ T, ∀ p' ∈ A, t'⁻¹ * p' ∈ R → p' ∈ jGroup A p) ∧ Case1 D p := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  rcases hc.case222 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy I.h222 D hq ht ht1 hp hρ with
    ⟨hle, -, h1 | h23 | h4'⟩ | hII
  · exact ⟨hle, h1⟩
  · exact absurd h23 (D.not_case23_of_isPrimary hpp)
  · exfalso
    obtain ⟨⟨ℓ, hpc⟩, -⟩ := h4'
    rcases D.suzukiType_of_isPrimary hpp hpc with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  · exfalso
    have := hII.2.2
    omega

end Config

end Sec3

namespace Case23Setup

variable {D : ClassicalModel A} {R T : Subgroup G} {p : G} {U W : Subgroup G} {y₁ y₂ : G}
  {ℓ : ℕ} (hS : Case23Setup D R T p U W y₁ y₂ ℓ) {g : G} (hc : Sec3 A R T g)
include hS hc

omit [Finite G] hc in
theorem typeA_of_mem_U {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) : ∃ k, D.SuzukiType u .a k := by
  rcases hS.types with ⟨-, -, hUa⟩ | ⟨-, hUa⟩
  · exact ⟨_, hUa u hu hu1⟩
  · exact ⟨_, hUa u hu hu1⟩

theorem exists_decomp (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) {t : G}
    (ht : t ∈ T) (ht1 : t ≠ 1) :
    ∃ τ ∈ R, ∃ u ∈ U, u ≠ 1 ∧ ∃ w ∈ W, w ≠ 1 ∧ t = τ * u * w := by
  obtain ⟨p', hp', hρ'⟩ := hc.exists_aPart h32 h4 h34 ht
  obtain ⟨hp'J, hp'U, hp'W⟩ := hS.aPart_mem_diagSet hc ht ht1 hp' hρ'
  have hJV := hS.jGroup_le_sec3V hc h32 h4 h34
  have htwo := Case23Setup.two hc h32
  obtain ⟨u, hu, w, hw, hp'eq⟩ := exists_mul_of_mem_sup htwo (hS.diag.U_le.trans hJV)
    (hS.diag.W_le.trans hJV) (hS.diag.J_eq ▸ hp'J)
  have hτR : p'⁻¹ * t ∈ R := by
    have := inv_mem hρ'
    simpa [mul_inv_rev] using this
  refine ⟨p'⁻¹ * t, hτR, u, hu, ?_, w, hw, ?_, ?_⟩
  · rintro rfl
    apply hp'W
    rw [← hp'eq, one_mul]
    exact hw
  · rintro rfl
    apply hp'U
    rw [← hp'eq, mul_one]
    exact hu
  · have hcomm : p' * (p'⁻¹ * t) = (p'⁻¹ * t) * p' :=
      hc.commute_V h32 (hJV hp'J) (hc.R_le_sec3V hτR)
    calc t = p' * (p'⁻¹ * t) := by group
      _ = (p'⁻¹ * t) * p' := hcomm
      _ = (p'⁻¹ * t) * u * w := by rw [← hp'eq]; group

theorem ne_of_decomp (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    {t t' τ τ' u u' w w' : G} (ht : t ∈ T) (ht' : t' ∈ T) (htt : t ≠ t') (hτ : τ ∈ R)
    (hτ' : τ' ∈ R) (hu : u ∈ U) (hu' : u' ∈ U) (hw : w ∈ W) (hw' : w' ∈ W)
    (he : t = τ * u * w) (he' : t' = τ' * u' * w') :
    u ≠ u' ∧ w ≠ w' := by
  have hZ := hS.oddCenter
  have hJV := hS.jGroup_le_sec3V hc h32 h4 h34
  have hJA : jGroup A p ≤ A := hS.vdata.le
  have hUV := hS.diag.U_le.trans hJV
  have hWV := hS.diag.W_le.trans hJV
  have hcV : ∀ x ∈ sec3V R T, ∀ y ∈ sec3V R T, x * y = y * x := fun x hx y hy =>
    hc.commute_V h32 hx hy
  have hs : t * t'⁻¹ ∈ T := mul_mem ht (inv_mem ht')
  have hs1 : t * t'⁻¹ ≠ 1 := fun h => htt (mul_inv_eq_one.mp h)
  obtain ⟨p', hp', hρ'⟩ := hc.exists_aPart h32 h4 h34 hs
  have hΓ := hS.aPart_mem_diagSet hc hs hs1 hp' hρ'
  constructor
  · rintro rfl
    have h1 : u * (w * w'⁻¹) = (w * w'⁻¹) * u :=
      hcV _ (hUV hu) _ (mul_mem (hWV hw) (inv_mem (hWV hw')))
    have h2 : (w * w'⁻¹) * τ'⁻¹ = τ'⁻¹ * (w * w'⁻¹) :=
      hcV _ (mul_mem (hWV hw) (inv_mem (hWV hw'))) _ (inv_mem (hc.R_le_sec3V hτ'))
    have he2 : t * t'⁻¹ = (τ * τ'⁻¹) * (w * w'⁻¹) := by
      calc t * t'⁻¹ = τ * (u * (w * w'⁻¹)) * u⁻¹ * τ'⁻¹ := by rw [he, he']; group
        _ = τ * ((w * w'⁻¹) * τ'⁻¹) := by rw [h1]; group
        _ = (τ * τ'⁻¹) * (w * w'⁻¹) := by rw [h2]; group
    have h3 := hc.aPart_eq_of_mul hZ hp' hρ' (mul_mem hτ (inv_mem hτ'))
      (hS.diag.W_le.trans hJA (mul_mem hw (inv_mem hw'))) he2
    exact hΓ.2.2 (h3 ▸ mul_mem hw (inv_mem hw'))
  · rintro rfl
    have h1 : (u * u'⁻¹) * τ'⁻¹ = τ'⁻¹ * (u * u'⁻¹) :=
      hcV _ (mul_mem (hUV hu) (inv_mem (hUV hu'))) _ (inv_mem (hc.R_le_sec3V hτ'))
    have he2 : t * t'⁻¹ = (τ * τ'⁻¹) * (u * u'⁻¹) := by
      calc t * t'⁻¹ = τ * ((u * u'⁻¹) * τ'⁻¹) := by rw [he, he']; group
        _ = (τ * τ'⁻¹) * (u * u'⁻¹) := by rw [h1]; group
    have h3 := hc.aPart_eq_of_mul hZ hp' hρ' (mul_mem hτ (inv_mem hτ'))
      (hS.diag.U_le.trans hJA (mul_mem hu (inv_mem hu'))) he2
    exact hΓ.2.1 (h3 ▸ mul_mem hu (inv_mem hu'))

theorem conj_le_sup_U (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) {a : G}
    (ha : a ∈ zpowers y₂) : rightConjugate T a ≤ T ⊔ U := by
  have haN : a ∈ A ⊓ normalizer (jGroup A p : Set G) := (zpowers_le.mpr hS.diag.y₂_mem) ha
  have haA : a ∈ A := (mem_inf.mp haN).1
  have haW : a ∈ centralizer (W : Set G) := (zpowers_le.mpr hS.diag.y₂_cent) ha
  have haU : a ∈ normalizer (U : Set G) := hS.diag.normalizer_le_U haN
  intro s hs
  rw [mem_rightConjugate_iff] at hs
  have hs' : s = a⁻¹ * (a * s * a⁻¹) * a := by group
  by_cases ht1 : a * s * a⁻¹ = 1
  · rw [hs', ht1]
    simp
  obtain ⟨τ, hτ, u, hu, -, w, hw, -, he⟩ := hS.exists_decomp hc h32 h4 h34 hs ht1
  have h1 : a⁻¹ * τ * a = τ := by
    have := (hc.commute_of_mem haA hτ).eq
    calc a⁻¹ * τ * a = a⁻¹ * (τ * a) := by group
      _ = a⁻¹ * (a * τ) := by rw [this]
      _ = τ := by group
  have h2 : a⁻¹ * w * a = w := by
    have := mem_centralizer_iff.mp haW w hw
    calc a⁻¹ * w * a = a⁻¹ * (w * a) := by group
      _ = a⁻¹ * (a * w) := by rw [this]
      _ = w := by group
  have hua : a⁻¹ * u * a ∈ U := by
    have := (mem_normalizer_iff.mp (inv_mem haU) u).mp hu
    simpa using this
  have h3 : w * (u⁻¹ * (a⁻¹ * u * a)) = (u⁻¹ * (a⁻¹ * u * a)) * w :=
    (hS.commute_U_W hc h32 h4 h34 (mul_mem (inv_mem hu) hua) hw).symm
  have h4' : s = (a * s * a⁻¹) * (u⁻¹ * (a⁻¹ * u * a)) := by
    calc s = a⁻¹ * (a * s * a⁻¹) * a := hs'
      _ = (a⁻¹ * τ * a) * (a⁻¹ * u * a) * (a⁻¹ * w * a) := by rw [he]; group
      _ = τ * u * (u⁻¹ * (a⁻¹ * u * a)) * w := by rw [h1, h2]; group
      _ = τ * u * (w * (u⁻¹ * (a⁻¹ * u * a))) := by rw [h3]; group
      _ = (a * s * a⁻¹) * (u⁻¹ * (a⁻¹ * u * a)) := by rw [he]; group
  rw [h4']
  exact mul_mem (mem_sup_left hs) (mem_sup_right (mul_mem (inv_mem hu) hua))

theorem conj_le_sup_W (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) {a : G}
    (ha : a ∈ zpowers y₁) : rightConjugate T a ≤ T ⊔ W := by
  have haN : a ∈ A ⊓ normalizer (jGroup A p : Set G) := (zpowers_le.mpr hS.diag.y₁_mem) ha
  have haA : a ∈ A := (mem_inf.mp haN).1
  have haU : a ∈ centralizer (U : Set G) := (zpowers_le.mpr hS.diag.y₁_cent) ha
  have haW : a ∈ normalizer (W : Set G) := hS.diag.normalizer_le_W haN
  intro s hs
  rw [mem_rightConjugate_iff] at hs
  have hs' : s = a⁻¹ * (a * s * a⁻¹) * a := by group
  by_cases ht1 : a * s * a⁻¹ = 1
  · rw [hs', ht1]
    simp
  obtain ⟨τ, hτ, u, hu, -, w, hw, -, he⟩ := hS.exists_decomp hc h32 h4 h34 hs ht1
  have h1 : a⁻¹ * τ * a = τ := by
    have := (hc.commute_of_mem haA hτ).eq
    calc a⁻¹ * τ * a = a⁻¹ * (τ * a) := by group
      _ = a⁻¹ * (a * τ) := by rw [this]
      _ = τ := by group
  have h2 : a⁻¹ * u * a = u := by
    have := mem_centralizer_iff.mp haU u hu
    calc a⁻¹ * u * a = a⁻¹ * (u * a) := by group
      _ = a⁻¹ * (a * u) := by rw [this]
      _ = u := by group
  have hwa : a⁻¹ * w * a ∈ W := by
    have := (mem_normalizer_iff.mp (inv_mem haW) w).mp hw
    simpa using this
  have h4' : s = (a * s * a⁻¹) * (w⁻¹ * (a⁻¹ * w * a)) := by
    calc s = a⁻¹ * (a * s * a⁻¹) * a := hs'
      _ = (a⁻¹ * τ * a) * (a⁻¹ * u * a) * (a⁻¹ * w * a) := by rw [he]; group
      _ = (a * s * a⁻¹) * (w⁻¹ * (a⁻¹ * w * a)) := by rw [h1, h2, he]; group
  rw [h4']
  exact mul_mem (mem_sup_left hs) (mem_sup_right (mul_mem (inv_mem hw) hwa))

theorem T_inf_sup_U (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) :
    T ⊓ (R ⊔ U) = ⊥ :=
  hc.inf_sup_eq_bot_of_aParts h32 h4 h34 hS.oddCenter (Case23Setup.two hc h32) hc.R_le_sec3V
    (hS.diag.U_le.trans (hS.jGroup_le_sec3V hc h32 h4 h34)) (hS.diag.U_le.trans hS.vdata.le)
    (fun _s hs hs1 _p' hp' hρ' => (hS.aPart_mem_diagSet hc hs hs1 hp' hρ').2.1)

theorem T_inf_sup_W (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) :
    T ⊓ (R ⊔ W) = ⊥ :=
  hc.inf_sup_eq_bot_of_aParts h32 h4 h34 hS.oddCenter (Case23Setup.two hc h32) hc.R_le_sec3V
    (hS.diag.W_le.trans (hS.jGroup_le_sec3V hc h32 h4 h34)) (hS.diag.W_le.trans hS.vdata.le)
    (fun _s hs hs1 _p' hp' hρ' => (hS.aPart_mem_diagSet hc hs hs1 hp' hρ').2.2)

theorem mem_of_mem_sup_of_mem {X : Subgroup G} (h32 : Lemma32) (hXV : X ≤ sec3V R T)
    (hXA : X ≤ A) {v : G} (hv : v ∈ R ⊔ X)
    (hvA : v ∈ A) : v ∈ X := by
  obtain ⟨r, hr, x, hx, rfl⟩ := exists_mul_of_mem_sup (Case23Setup.two hc h32) hc.R_le_sec3V hXV
    hv
  have hrA : r ∈ A := by simpa using mul_mem hvA (inv_mem (hXA hx))
  have hr1 : r ∈ R ⊓ A := mem_inf.mpr ⟨hr, hrA⟩
  rw [hc.R_inf_A hS.oddCenter, mem_bot] at hr1
  rw [hr1, one_mul]
  exact hx

section Config

variable (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A))
  (hfam : D.family = .symplectic) (hq : 4 ≤ D.q)
include I hTy hfam hq

theorem cover_U (hAP : SymplecticTypeAPerfect) {x : G}
    (hx : x ∈ normalizer (sec3V R T : Set G)) (hne : rightConjugate R x ≠ R)
    (hle : rightConjugate R x ≤ R ⊔ U) :
    ∀ v ∈ R ⊔ U, v ∉ U → ∃ z : G, rightConjugate R z ≤ R ⊔ U ∧ v ∈ rightConjugate R z := by
  have hZ := hS.oddCenter
  have hJV := hS.jGroup_le_sec3V hc I.h32 I.h4 I.h34
  have hUA : U ≤ A := hS.diag.U_le.trans hS.vdata.le
  have h' := hc.of_mem_normalizer I.h32 hx hne
  obtain ⟨s, hs, hs1, u, hu, hu1, hρ'⟩ := h'.exists_aPart_mem_of_le I.h32 I.h4 I.h34 hZ
    (Case23Setup.two hc I.h32) hc.R_le_sec3V (hS.diag.U_le.trans hJV) hUA hle
  obtain ⟨k, hk⟩ := hS.typeA_of_mem_U hu hu1
  obtain ⟨⟨y, hJ⟩, ⟨p₁, y', hJ'⟩, -⟩ :=
    h'.exists_jData_pair_of_typeA I hTy D hfam hq hs hs1 (hUA hu) hρ' hk
  have h1 := h'.case1_of_typeA I hTy D hq hs hs1 (hUA hu) hρ' hk
  have hV'' : sec3V R (rightConjugate R x) = R ⊔ U := by
    rw [h'.sec3V_eq_sup I.h32 I.h4 I.h34 hJ, h1.1, hS.alpha_U u hu hu1]
  rcases h'.cover_of_jData I.h32 I.h4 I.h34 hJ hJ' with h2 | h2
  · exfalso
    have hsA : s ∈ A := by
      rw [h2] at hs
      exact (mem_inf.mp hs).2
    have hsU := hS.mem_of_mem_sup_of_mem hc I.h32 (hS.diag.U_le.trans hJV) hUA
      (hle hs) hsA
    obtain ⟨k', hk'⟩ := hS.typeA_of_mem_U hsU hs1
    exact h'.false_of_mem_typeA I hTy D hfam hq hAP hs hs1 hk'
  · intro v hv hvU
    have hvA : v ∉ A := fun h => hvU (hS.mem_of_mem_sup_of_mem hc I.h32
      (hS.diag.U_le.trans hJV) hUA hv h)
    obtain ⟨z, hz, hvz⟩ := h2 v (hV''.symm ▸ hv) hvA
    exact ⟨z, hV'' ▸ hz, hvz⟩

theorem cover_W (h117 : ClassicalPrimaryPerfect) {x : G}
    (hx : x ∈ normalizer (sec3V R T : Set G)) (hne : rightConjugate R x ≠ R)
    (hle : rightConjugate R x ≤ R ⊔ W) :
    ∀ v ∈ R ⊔ W, v ∉ W → ∃ z : G, rightConjugate R z ≤ R ⊔ W ∧ v ∈ rightConjugate R z := by
  have hZ := hS.oddCenter
  have hJV := hS.jGroup_le_sec3V hc I.h32 I.h4 I.h34
  have hWA : W ≤ A := hS.diag.W_le.trans hS.vdata.le
  have h' := hc.of_mem_normalizer I.h32 hx hne
  obtain ⟨s, hs, hs1, w, hw, hw1, hρ'⟩ := h'.exists_aPart_mem_of_le I.h32 I.h4 I.h34 hZ
    (Case23Setup.two hc I.h32) hc.R_le_sec3V (hS.diag.W_le.trans hJV) hWA hle
  have hwp := hS.prim_W w hw hw1
  obtain ⟨hle', h1⟩ := h'.case1_of_isPrimary I hTy D hq hs hs1 (hWA hw) hρ' hwp
  obtain ⟨⟨y, hJ⟩, ⟨p₁, y', hJ'⟩, -⟩ :=
    h'.exists_jData_pair_of_case14 I hTy D hfam hq hs hs1 (hWA hw) hρ' hle' (Or.inl h1)
  have hV'' : sec3V R (rightConjugate R x) = R ⊔ W := by
    rw [h'.sec3V_eq_sup I.h32 I.h4 I.h34 hJ, h1.1, hS.alpha_W w hw hw1]
  rcases h'.cover_of_jData I.h32 I.h4 I.h34 hJ hJ' with h2 | h2
  · exfalso
    have hsA : s ∈ A := by
      rw [h2] at hs
      exact (mem_inf.mp hs).2
    have hsW := hS.mem_of_mem_sup_of_mem hc I.h32 (hS.diag.W_le.trans hJV) hWA
      (hle hs) hsA
    exact h'.false_of_mem_primary I hTy D hq h117 hs hs1 (hS.prim_W s hsW hs1)
  · intro v hv hvW
    have hvA : v ∉ A := fun h => hvW (hS.mem_of_mem_sup_of_mem hc I.h32
      (hS.diag.W_le.trans hJV) hWA hv h)
    obtain ⟨z, hz, hvz⟩ := h2 v (hV''.symm ▸ hv) hvA
    exact ⟨z, hV'' ▸ hz, hvz⟩

end Config

end Case23Setup

end CFSG.ComponentClassification.RankTwoClassical
