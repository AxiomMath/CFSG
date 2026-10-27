module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseDSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseC
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec5G

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AS76b.Sec5 (exists_mul_of_mem_sup)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

namespace ClassicalModel

omit [Finite G] in
theorem hasMeasure_of_suzukiType_b (D : ClassicalModel A) {x : G} {ℓ : ℕ}
    (h : D.SuzukiType x .b ℓ) (hℓ : 1 < ℓ) (hfam : D.family = .symplectic) :
    D.HasMeasure x (3 * ℓ + 2) := by
  have hr := D.hasRank_of_suzukiType h
  refine ⟨ℓ, hr, Or.inr (Or.inr ⟨fun hp => ?_, fun ⟨k, hk⟩ => ?_, rfl⟩)⟩
  · cases D with
    | linear => exact h.elim
    | unitary => exact h.elim
    | symplectic =>
      have := ClassicalModel.hasRank_unique _ hr hp
      omega
    | orthPlus => simp [family] at hfam
    | orthMinus => simp [family] at hfam
  · have := (D.suzukiType_unique h hk).1
    cases this

omit [Finite G] in
theorem hasMeasure_of_suzukiType_a (D : ClassicalModel A) {x : G} {ℓ : ℕ}
    (h : D.SuzukiType x .a ℓ) (hℓ : 1 < ℓ) (hfam : D.family = .symplectic) :
    D.HasMeasure x (3 * ℓ + 2) := by
  have hr := D.hasRank_of_suzukiType h
  refine ⟨ℓ, hr, Or.inr (Or.inr ⟨fun hp => ?_, fun ⟨k, hk⟩ => ?_, rfl⟩)⟩
  · cases D with
    | linear => exact h.elim
    | unitary => exact h.elim
    | symplectic =>
      have := ClassicalModel.hasRank_unique _ hr hp
      omega
    | orthPlus => simp [family] at hfam
    | orthMinus => simp [family] at hfam
  · have := (D.suzukiType_unique h hk).1
    cases this

omit [Finite G] in
theorem hasMeasure_three_of_isPrimary (D : ClassicalModel A) (hfam : D.family = .symplectic)
    {x : G} (hx : D.IsPrimary x) : D.HasMeasure x 3 := by
  have hr : D.HasRank x 1 := by
    cases D with
    | linear => simp [family] at hfam
    | unitary => simp [family] at hfam
    | symplectic => exact hx
    | orthPlus => simp [family] at hfam
    | orthMinus => simp [family] at hfam
  exact D.hasMeasure_of_isPrimary hr hx

end ClassicalModel

namespace Sec3

variable {R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem R_le_sec3V : R ≤ sec3V R T := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  exact le_sup_left.trans (le_sec3V_of ⟨w, hw⟩)

theorem T_le_sec3V : T ≤ sec3V R T := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  exact le_sup_right.trans (le_sec3V_of ⟨w, hw⟩)

theorem isElemAbelian_V (h32 : Lemma32) : IsElemAbelian 2 (sec3V R T) := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  exact isElemAbelian_sec3V (hc.elemR h32) hc.le_centralizer ⟨w, hw⟩

theorem commute_V (h32 : Lemma32) {x y : G} (hx : x ∈ sec3V R T) (hy : y ∈ sec3V R T) :
    x * y = y * x :=
  congrArg Subtype.val ((hc.isElemAbelian_V h32).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem sec3V_le_centralizer_R (h32 : Lemma32) : sec3V R T ≤ centralizer (R : Set G) := by
  intro v hv
  rw [mem_centralizer_iff]
  intro r hr
  exact hc.commute_V h32 (hc.R_le_sec3V hr) hv

theorem of_mem_normalizer (h32 : Lemma32) {x : G} (hx : x ∈ normalizer (sec3V R T : Set G))
    (hne : rightConjugate R x ≠ R) : Sec3 A R (rightConjugate R x) x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRxV : rightConjugate R x ≤ sec3V R T := Lemma36.rightConjugate_le hc.R_le_sec3V hx
  have hRxC := hRxV.trans (hc.sec3V_le_centralizer_R h32)
  refine ⟨hc.hyp, hc.sylowR, fun hxA => hne ?_,
    AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowR x, hRxC⟩
  have hK : rightConjugate (centralizer (A : Set G)) x = centralizer (A : Set G) := by
    rw [← centralizer_rightConjugate, (rightConjugate_eq_self_iff A x).mpr hxA]
  have hRxK : rightConjugate R x ≤ centralizer (A : Set G) := hK ▸ map_mono hc.sylowR.le
  have hp : IsPGroup 2 ↥(R ⊔ rightConjugate R x) :=
    IsPGroup.to_sup_of_normal_left' hc.sylowR.isPGroup (hc.sylowR.isPGroup.map _)
      (hRxC.trans (centralizer_le_normalizer _))
  have h1 : R ⊔ rightConjugate R x = R :=
    hc.sylowR.eq_of_le le_sup_left (sup_le hc.sylowR.le hRxK) hp
  exact eq_of_le_of_card_ge (le_sup_right.trans h1.le) (by rw [rightConjugate_card])

theorem aPart_eq_of_mul (hZ : Odd (Nat.card (center ↥A))) {s p r u : G} (hp : p ∈ A)
    (hρ : s⁻¹ * p ∈ R) (hr : r ∈ R) (hu : u ∈ A) (hs : s = r * u) : p = u := by
  refine hc.aPart_unique hZ hp hρ hu ?_
  have hcomm : Commute u r⁻¹ := hc.commute_of_mem hu (inv_mem hr)
  rw [hs, mul_inv_rev, mul_assoc, ← hcomm.eq, inv_mul_cancel_left]
  exact inv_mem hr

theorem inf_eq_bot_or_le_of_typeA (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A))
    (D : ClassicalModel A) (hfam : D.family = .symplectic) (hq : 4 ≤ D.q) {t p : G}
    (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) {k : ℕ}
    (hpa : D.SuzukiType p .a k) : T ⊓ A = ⊥ ∨ T ≤ A := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  have hZ : Odd (Nat.card (center ↥A)) :=
    (I.h222.conclusion D hq (hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)).1
  obtain ⟨hle, hI⟩ : (∀ t' ∈ T, ∀ p' ∈ A, t'⁻¹ * p' ∈ R → p' ∈ jGroup A p) ∧
      (Case1 D p ∨ Case4 D p) := by
    rcases hc.case222 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy I.h222 D hq ht ht1 hp hρ with
      ⟨hle, -, h1 | h23 | h4'⟩ | hII
    · exact ⟨hle, Or.inl h1⟩
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
  have hsyl := I.hJS.jSylowAt D hc.hyp.standard.1 hZ hq hp (hc.orderOf_aPart I.h32 ht ht1 hρ)
  obtain ⟨hreg, hcyc⟩ : RegularOn A (jGroup A p) (nonidentity (jGroup A p)) ∧
      AutCyclic A (jGroup A p) (D.q - 1) := by
    rcases hI with ⟨-, hreg, hcyc⟩ | ⟨-, hreg, hcyc⟩
    · exact ⟨hreg, hcyc⟩
    · exact ⟨hreg, hcyc⟩
  obtain ⟨y, hJ⟩ := hc.jData_of ht ht1 hp hρ hle hreg hcyc hsyl
  have hcardV : Nat.card ↥(sec3V R T ⊓ A) = D.q :=
    hc.card_inf_of_case14 I.h32 I.h4 I.h34 D hq ht ht1 hp hρ hle hI hsyl
  have hsw := hc.swap
  obtain ⟨t₁, ht₁, ht₁1⟩ := (rightConjugate R g⁻¹).bot_or_exists_ne_one.resolve_left
    hsw.T_ne_bot
  obtain ⟨p₁, hp₁, hρ₁⟩ := hsw.exists_aPart I.h32 I.h4 I.h34 ht₁
  have hJ' : ∃ y', JData A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p₁ (jGroup A p₁) y' := by
    rcases hsw.case222 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy I.h222 D hq ht₁ ht₁1 hp₁ hρ₁ with
      ⟨hle₁, -, hI₁⟩ | hII
    · have hsyl₁ := I.hJS.jSylowAt D hc.hyp.standard.1 hZ hq hp₁
        (hsw.orderOf_aPart I.h32 ht₁ ht₁1 hρ₁)
      rcases hI₁ with h1 | h23 | h4'
      · exact hsw.jData_of ht₁ ht₁1 hp₁ hρ₁ hle₁ h1.2.1 h1.2.2 hsyl₁
      · exfalso
        obtain ⟨U₁, W₁, z₁, z₂, ℓ₁, hS₁⟩ :=
          hsw.exists_case23Setup I hTy D hfam hq ht₁ ht₁1 hp₁ hρ₁ h23
        have h1 := hS₁.card_inf_sec3V hsw I.h32 I.h4 I.h34
        rw [hc.card_inf_sec3V_swap I.h32 I.h4 I.h34 hZ, hcardV] at h1
        nlinarith
      · exact hsw.jData_of ht₁ ht₁1 hp₁ hρ₁ hle₁ h4'.2.1 h4'.2.2 hsyl₁
    · exfalso
      have := hII.2.2
      omega
  obtain ⟨y', hJ'⟩ := hJ'
  rcases hc.dichotomy I.h32 I.h4 I.h34 hJ hJ' with h | h
  · exact Or.inl h
  · exact Or.inr (h.le.trans inf_le_right)

end Sec3

section CaseD

variable {R T : Subgroup G} {g : G}

theorem Sec3.exists_not_le (hc : Sec3 A R T g) (I : Inputs74)
    (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) (D : ClassicalModel A)
    (hfam : D.family = .symplectic) (hq : 4 ≤ D.q) {p : G} {U W : Subgroup G} {y₁ y₂ : G}
    {ℓ : ℕ} (hS : Case23Setup D R T p U W y₁ y₂ ℓ)
    (hno : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ¬ T' ≤ A) :
    ∃ x ∈ normalizer (sec3V R T : Set G), ¬ rightConjugate R x ≤ R ⊔ U := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  have hZ := hS.oddCenter
  have hsw := hc.swap
  obtain ⟨w₀, hw₀⟩ := hc.exists_conj
  obtain ⟨t₁, ht₁, ht₁1⟩ := (rightConjugate R g⁻¹).bot_or_exists_ne_one.resolve_left
    hsw.T_ne_bot
  obtain ⟨p₁, hp₁, hρ₁⟩ := hsw.exists_aPart I.h32 I.h4 I.h34 ht₁
  have hcardV := hS.card_inf_sec3V hc I.h32 I.h4 I.h34
  obtain ⟨U₁, W₁, z₁, z₂, ℓ₁, hS₁⟩ :
      ∃ (U₁ W₁ : Subgroup G) (z₁ z₂ : G) (ℓ₁ : ℕ),
        Case23Setup D (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p₁ U₁ W₁ z₁ z₂ ℓ₁ := by
    rcases hsw.case222 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy I.h222 D hq ht₁ ht₁1 hp₁ hρ₁ with
      ⟨hle₁, -, hI₁⟩ | hII
    · rcases hI₁ with h1 | h23 | h4'
      · exfalso
        have hsyl₁ := I.hJS.jSylowAt D hc.hyp.standard.1 hZ hq hp₁
          (hsw.orderOf_aPart I.h32 ht₁ ht₁1 hρ₁)
        have h2 := hsw.card_inf_of_case14 I.h32 I.h4 I.h34 D hq ht₁ ht₁1 hp₁ hρ₁ hle₁
          (Or.inl h1) hsyl₁
        rw [hc.card_inf_sec3V_swap I.h32 I.h4 I.h34 hZ, hcardV] at h2
        nlinarith
      · exact hsw.exists_case23Setup I hTy D hfam hq ht₁ ht₁1 hp₁ hρ₁ h23
      · exfalso
        have hsyl₁ := I.hJS.jSylowAt D hc.hyp.standard.1 hZ hq hp₁
          (hsw.orderOf_aPart I.h32 ht₁ ht₁1 hρ₁)
        have h2 := hsw.card_inf_of_case14 I.h32 I.h4 I.h34 D hq ht₁ ht₁1 hp₁ hρ₁ hle₁
          (Or.inr h4') hsyl₁
        rw [hc.card_inf_sec3V_swap I.h32 I.h4 I.h34 hZ, hcardV] at h2
        nlinarith
    · exfalso
      have := hII.2.2
      omega
  set R₁ := rightConjugate T g⁻¹ with hR₁
  set T₁ := rightConjugate R g⁻¹ with hT₁
  set J₁ := jGroup A p₁ with hJ₁
  have hV₁ : sec3V R₁ T₁ = rightConjugate (sec3V R T) g⁻¹ := by
    rw [hR₁, hT₁, sec3V_rightConjugate, sec3V_symm hw₀]
  have hVJ₁ : sec3V R₁ T₁ ⊓ A = J₁ := hS₁.inf_sec3V_eq hsw I.h32 I.h4 I.h34
  have hVeq₁ : sec3V R₁ T₁ = R₁ ⊔ J₁ := hS₁.sec3V_eq_sup hsw I.h32 I.h4 I.h34
  have htwo₁ : ∀ v ∈ sec3V R₁ T₁, v * v = 1 := fun v hv => by
    have := (hsw.isElemAbelian_V I.h32).2 v hv
    rwa [sq] at this
  have hJ₁V : J₁ ≤ sec3V R₁ T₁ := hS₁.jGroup_le_sec3V hsw I.h32 I.h4 I.h34
  have hp₁Γ := hS₁.aPart_mem_diagSet hsw ht₁ ht₁1 hp₁ hρ₁
  obtain ⟨hp₁J, hp₁U, hp₁W⟩ := hp₁Γ
  obtain ⟨u₁, hu₁, w₁, hw₁, hp₁eq⟩ := exists_mul_of_mem_sup htwo₁
    ((hS₁.diag.U_le).trans hJ₁V) ((hS₁.diag.W_le).trans hJ₁V) (hS₁.diag.J_eq ▸ hp₁J)
  have hu₁1 : u₁ ≠ 1 := by
    rintro rfl
    apply hp₁W
    rw [← hp₁eq, one_mul]
    exact hw₁
  have hw₁1 : w₁ ≠ 1 := by
    rintro rfl
    apply hp₁U
    rw [← hp₁eq, mul_one]
    exact hu₁
  set τ := p₁⁻¹ * t₁ with hτ
  have hτR : τ ∈ R₁ := by
    have := inv_mem hρ₁
    simpa [hτ, mul_inv_rev] using this
  have hτK : τ ∈ centralizer (A : Set G) := hsw.sylowR.le hτR
  have ht₁eq : t₁ = τ * u₁ * w₁ := by
    have hcomm : p₁ * τ = τ * p₁ :=
      (hsw.commute_V I.h32 (hJ₁V hp₁J) (hsw.R_le_sec3V hτR))
    calc t₁ = p₁ * τ := by rw [hτ]; group
      _ = τ * p₁ := hcomm
      _ = τ * u₁ * w₁ := by rw [← hp₁eq]; group
  have hz₁A : z₁ ∈ A := (mem_inf.mp hS₁.diag.y₁_mem).1
  have hz₂A : z₂ ∈ A := (mem_inf.mp hS₁.diag.y₂_mem).1
  have hz₁τ : z₁ * τ = τ * z₁ := mem_centralizer_iff.mp hτK z₁ hz₁A
  have hz₂τ : z₂ * τ = τ * z₂ := mem_centralizer_iff.mp hτK z₂ hz₂A
  have hzN : ∀ a ∈ (zpowers z₁ : Set G) ∪ zpowers z₂,
      g⁻¹ * a * g ∈ normalizer (sec3V R T : Set G) := by
    have hN₁ : ∀ a ∈ A ⊓ normalizer (J₁ : Set G), a ∈ normalizer (sec3V R₁ T₁ : Set G) := by
      intro a ha
      rw [hVeq₁]
      refine mem_normalizer_sup (centralizer_le_normalizer _ ?_) (mem_inf.mp ha).2
      rw [mem_centralizer_iff]
      intro r hr
      exact (mem_centralizer_iff.mp (hsw.sylowR.le hr) a (mem_inf.mp ha).1).symm
    intro a ha
    have haN : a ∈ A ⊓ normalizer (J₁ : Set G) := by
      rcases ha with ha | ha
      · exact (zpowers_le.mpr hS₁.diag.y₁_mem) ha
      · exact (zpowers_le.mpr hS₁.diag.y₂_mem) ha
    have h1 := hN₁ a haN
    rw [hV₁, mem_normalizer_rightConjugate_iff] at h1
    simpa using h1
  by_contra hall
  push Not at hall
  set Q₁ := rightConjugate (R ⊔ U) g⁻¹ with hQ₁
  have hRU : R ≤ R ⊔ U := le_sup_left
  have hrQ : τ * u₁ * w₁ ∈ Q₁ := by
    rw [← ht₁eq]
    exact map_mono hRU ht₁
  have hQ : ∀ a ∈ (zpowers z₁ : Set G) ∪ zpowers z₂, a⁻¹ * (τ * u₁ * w₁) * a ∈ Q₁ := by
    intro a ha
    have h1 := hall _ (hzN a ha)
    rw [← ht₁eq]
    have h2 : a⁻¹ * t₁ * a ∈ rightConjugate (rightConjugate R (g⁻¹ * a * g)) g⁻¹ := by
      rw [rightConjugate_mul, mem_rightConjugate_iff]
      rw [hT₁, mem_rightConjugate_iff] at ht₁
      have : g⁻¹ * a * g * g⁻¹ = g⁻¹ * a := by group
      rw [this]
      simpa [mul_assoc] using ht₁
    exact map_mono h1 h2
  obtain ⟨hUQ, hWQ⟩ := le_of_forall_conj_le
    (fun x hx z hz => hS₁.commute_U_W hsw I.h32 I.h4 I.h34 hx hz) hu₁ hw₁
    hS₁.diag.three_le_U hS₁.diag.three_le_W hz₁τ hz₂τ hS₁.diag.y₁_cent hS₁.diag.y₂_cent
    (fun u' hu' hu'1 => hS₁.diag.trans_U hu₁ hu₁1 hu' hu'1)
    (fun w' hw' hw'1 => hS₁.diag.trans_W hw₁ hw₁1 hw' hw'1) hrQ hQ
  have hJQ : J₁ ≤ Q₁ := (le_of_eq hS₁.diag.J_eq).trans (sup_le hUQ hWQ)
  have hVAg : sec3V R T ⊓ rightConjugate A g ≤ R ⊔ U := by
    have h1 : rightConjugate J₁ g ≤ R ⊔ U := by
      have := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hJQ
      change rightConjugate J₁ g ≤ rightConjugate Q₁ g at this
      rwa [hQ₁, rightConjugate_inv_rightConjugate] at this
    have h2 : rightConjugate J₁ g = sec3V R T ⊓ rightConjugate A g := by
      rw [← hVJ₁, hV₁, rightConjugate_inf, rightConjugate_inv_rightConjugate]
    rwa [h2] at h1
  have hRUT : (R ⊔ U) ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    rw [mem_bot]
    by_contra hs1
    obtain ⟨hsRU, hsT⟩ := mem_inf.mp hs
    obtain ⟨r, hr, u, hu, rfl⟩ := exists_mul_of_mem_sup (fun v hv => by
        have := (hc.isElemAbelian_V I.h32).2 v hv
        rwa [sq] at this) hc.R_le_sec3V
      ((hS.diag.U_le).trans (hS.jGroup_le_sec3V hc I.h32 I.h4 I.h34)) hsRU
    obtain ⟨p', hp'A, hρ'⟩ := hc.exists_aPart I.h32 I.h4 I.h34 hsT
    have hp'u : p' = u := hc.aPart_eq_of_mul hZ hp'A hρ' hr
      (hS.vdata.le (hS.diag.U_le hu)) rfl
    have hΓ := hS.aPart_mem_diagSet hc hsT hs1 hp'A hρ'
    exact hΓ.2.1 (hp'u ▸ hu)
  have hRUle : R ⊔ U ≤ sec3V R T ⊓ rightConjugate A g := by
    intro x hx
    have hxV : x ∈ sec3V R T := (sup_le hc.R_le_sec3V
      ((hS.diag.U_le).trans (hS.jGroup_le_sec3V hc I.h32 I.h4 I.h34))) hx
    have hV := (lemma35 I.h32 (lemma33Two_of I.h32 I.h4 I.h34) hc.hyp hc.sylowR hc.sylowT
      hc.le_centralizer).2.2
    have htwo : ∀ v ∈ sec3V R T, v * v = 1 := fun v hv => by
      have := (hc.isElemAbelian_V I.h32).2 v hv
      rwa [sq] at this
    have hxV' : x ∈ T ⊔ (sec3V R T ⊓ rightConjugate A g) := by
      rw [← hV]
      exact hxV
    obtain ⟨t, ht, j, hj, rfl⟩ := exists_mul_of_mem_sup htwo hc.T_le_sec3V inf_le_left hxV'
    have htRU : t ∈ R ⊔ U := by
      have := mul_mem hx (inv_mem (hVAg hj))
      simpa using this
    have ht1 : t ∈ (R ⊔ U) ⊓ T := mem_inf.mpr ⟨htRU, ht⟩
    rw [hRUT, mem_bot] at ht1
    rw [ht1, one_mul]
    exact hj
  have hRA : rightConjugate R g⁻¹ ≤ A := by
    intro r hr
    rw [mem_rightConjugate_iff, inv_inv] at hr
    have h1 := (mem_inf.mp (hRUle (mem_sup_left hr))).2
    rw [mem_rightConjugate_iff] at h1
    simpa [mul_assoc] using h1
  exact hno _ _ (hc.sec3_of_le I.h32 hZ hRA) hRA


end CaseD

end CFSG.ComponentClassification.RankTwoClassical
