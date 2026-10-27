module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseDInside
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseDOutside

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AS76b.Sec5
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.Goldschmidt AS76b.Lemma36

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

namespace Sec3

variable {R T : Subgroup G} {g : G}

theorem exists_transport {R₀ T' : Subgroup G} {x : G} (h' : Sec3 A R₀ T' x)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) :
    ∃ k ∈ centralizer (A : Set G), Sec3 A R (rightConjugate T' k) (x * k) ∧
      ∀ s q : G, s⁻¹ * q ∈ R₀ → q ∈ A → (k⁻¹ * s * k)⁻¹ * q ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkK, hk⟩ := hR.exists_mem_conj h'.sylowR
  have hkA : k ∈ normalizer (A : Set G) := centralizer_le_normalizer _ hkK
  have hR₀ : rightConjugate R₀ k = R := by
    ext y
    rw [mem_rightConjugate_iff, hk, show k⁻¹ * (k * y * k⁻¹) * k = y by group]
  refine ⟨k, hkK, ⟨h'.hyp, hR, fun hxk => h'.not_mem ?_, ?_, ?_⟩, fun s q hsq hq => ?_⟩
  · rw [show x = x * k * k⁻¹ by group]
    exact mul_mem hxk (inv_mem hkA)
  · have h := AschbacherTheorem3.isSylowOf_rightConjugate h'.sylowT k
    rwa [rightConjugate_mul] at h
  · rw [← hR₀, centralizer_rightConjugate]
    exact map_mono h'.le_centralizer
  · have hkq : q * k = k * q := mem_centralizer_iff.mp hkK q hq
    have h1 := (hk _).mp hsq
    have h2 : (k⁻¹ * s * k)⁻¹ * q = k⁻¹ * (s⁻¹ * q) * k := by
      calc (k⁻¹ * s * k)⁻¹ * q = k⁻¹ * s⁻¹ * (k * q) := by group
        _ = k⁻¹ * s⁻¹ * (q * k) := by rw [hkq]
        _ = k⁻¹ * (s⁻¹ * q) * k := by group
    rw [h2]
    exact h1

theorem cover_of_jData (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) {p y p' y' : G} {J J' : Subgroup G} (hJ : JData A R T p J y)
    (hJ' : JData A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p' J' y') :
    T = sec3V R T ⊓ A ∨ ∀ v ∈ sec3V R T, v ∉ A →
      ∃ x : G, rightConjugate R x ≤ sec3V R T ∧ v ∈ rightConjugate R x := by
  have hp := hc.pairData_RT h32 h4 h34 hJ hJ'
  by_cases hX : ∀ x ∈ pairGroup (sec3V R T) A (rightConjugate A g), conjSub x R = R
  · exact Or.inl (hp.eq_of_normalizes hX).1
  · push Not at hX
    obtain ⟨x₀, hx₀, hx₀R⟩ := hX
    obtain ⟨-, hcov⟩ := hp.case_three₁ hx₀ hx₀R
    refine Or.inr fun v hv hvA => ?_
    obtain ⟨x, hx, hvx, -⟩ := (hcov v hv).mp fun h => hvA (mem_inf.mp h).2
    exact ⟨x, rightConjugate_le hp.d₁.le (pairGroup_le hx), hvx⟩

section Config

variable (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) (D : ClassicalModel A)
  (hfam : D.family = .symplectic) (hq : 4 ≤ D.q)
include I hTy hfam hq

theorem cover_of_case23 (hc : Sec3 A R T g) {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A)
    (hρ : t⁻¹ * p ∈ R) (h23 : Case23 D p)
    (hno : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ¬ T' ≤ A)
    (hprim : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ∀ s ∈ T', s ≠ 1 → ∀ p' ∈ A,
      s⁻¹ * p' ∈ R → ¬ D.IsPrimary p') :
    ∀ v ∈ sec3V R T, v ∉ A →
      ∃ x : G, rightConjugate R x ≤ sec3V R T ∧ v ∈ rightConjugate R x := by
  obtain ⟨U, W, y₁, y₂, ℓ, hS⟩ := hc.exists_case23Setup I hTy D hfam hq ht ht1 hp hρ h23
  have hZ := hS.oddCenter
  have hJV := hS.jGroup_le_sec3V hc I.h32 I.h4 I.h34
  have hJA : jGroup A p ≤ A := hS.vdata.le
  have htwo := Case23Setup.two hc I.h32
  have hWbad : ∀ x ∈ normalizer (sec3V R T : Set G), rightConjugate R x ≠ R →
      rightConjugate R x ≤ R ⊔ W → False := by
    intro x hx hne hle
    have h' := hc.of_mem_normalizer I.h32 hx hne
    obtain ⟨s, hs, hs1, w, hw, hw1, hρ'⟩ := h'.exists_aPart_mem_of_le I.h32 I.h4 I.h34 hZ htwo
      hc.R_le_sec3V (hS.diag.W_le.trans hJV) (hS.diag.W_le.trans hJA) hle
    exact hprim _ x h' s hs hs1 w (hS.diag.W_le.trans hJA hw) hρ' (hS.prim_W w hw hw1)
  have hU : ∀ x ∈ normalizer (sec3V R T : Set G), rightConjugate R x ≠ R →
      rightConjugate R x ≤ R ⊔ U → rightConjugate R x ⊓ U = ⊥ := by
    intro x hx hne _
    have h' := hc.of_mem_normalizer I.h32 hx hne
    by_contra hUne
    obtain ⟨u, hu, hu1⟩ := (rightConjugate R x ⊓ U).bot_or_exists_ne_one.resolve_left hUne
    obtain ⟨huT, huU⟩ := mem_inf.mp hu
    have huA : u ∈ A := hS.diag.U_le.trans hJA huU
    obtain ⟨k, hk⟩ : ∃ k, D.SuzukiType u .a k := by
      rcases hS.types with ⟨-, -, hUa⟩ | ⟨-, hUa⟩
      · exact ⟨_, hUa u huU hu1⟩
      · exact ⟨_, hUa u huU hu1⟩
    rcases h'.inf_eq_bot_or_le_of_typeA I hTy D hfam hq huT hu1 huA
      (by rw [inv_mul_cancel]; exact one_mem _) hk with h | h
    · have h1 : u ∈ rightConjugate R x ⊓ A := mem_inf.mpr ⟨huT, huA⟩
      rw [h, mem_bot] at h1
      exact hu1 h1
    · exact hno _ x h' h
  have h3 : ∃ T' ∈ gMembers (normalizer (sec3V R T : Set G)) R, T' ≠ R ∧
      T' ⊓ (R ⊔ U) = ⊥ ∧ T' ⊓ (R ⊔ W) = ⊥ := by
    obtain ⟨x, hx, hnle⟩ := hc.exists_not_le I hTy D hfam hq hS hno
    have hne : rightConjugate R x ≠ R := by
      intro h
      apply hnle
      rw [h]
      exact le_sup_left
    have h' := hc.of_mem_normalizer I.h32 hx hne
    have hT'V := Lemma36.rightConjugate_le hc.R_le_sec3V hx
    refine ⟨rightConjugate R x, ⟨x, hx, rfl⟩, hne, ?_⟩
    rcases hS.trichotomy hc I hTy h' hT'V with hU' | hW' | hΓ
    · exact absurd (h'.le_sup_of_aParts I.h32 I.h4 I.h34 hU') hnle
    · exact (hWbad x hx hne (h'.le_sup_of_aParts I.h32 I.h4 I.h34 hW')).elim
    · exact ⟨h'.inf_sup_eq_bot_of_aParts I.h32 I.h4 I.h34 hZ htwo hc.R_le_sec3V
        (hS.diag.U_le.trans hJV) (hS.diag.U_le.trans hJA)
        (fun s hs hs1 p' hp' hρ' => (hΓ s hs hs1 p' hp' hρ').1),
        h'.inf_sup_eq_bot_of_aParts I.h32 I.h4 I.h34 hZ htwo hc.R_le_sec3V
        (hS.diag.W_le.trans hJV) (hS.diag.W_le.trans hJA)
        (fun s hs hs1 p' hp' hρ' => (hΓ s hs hs1 p' hp' hρ').2)⟩
  have hG := hS.gHyp51 hc I hTy (fun x hx hne hle => Or.inr (hU x hx hne hle))
    (fun x hx hne hle => (hWbad x hx hne hle).elim) h3
  rcases fusionLemmaG_rot hG with ⟨hSig, -, -⟩ | ⟨-, -, -, x, hx, hWx⟩
  · intro v hv hvA
    have hUW : (U ⊔ W : Subgroup G) ≤ A := by
      rw [← hS.diag.J_eq]
      exact hJA
    have hvSig : v ∈ gFused (normalizer (sec3V R T : Set G)) R := by
      rw [hSig]
      exact ⟨hv, fun hvUW => hvA (hUW hvUW)⟩
    obtain ⟨x, hx, r, hr, -, rfl⟩ := hvSig
    refine ⟨x, Lemma36.rightConjugate_le hc.R_le_sec3V hx, ?_⟩
    rw [mem_rightConjugate_iff, show x * (x⁻¹ * r * x) * x⁻¹ = r by group]
    exact hr
  · exfalso
    have hWA' : rightConjugate R x ≤ A := by
      rw [hWx]
      exact hS.diag.W_le.trans hJA
    exact hno _ _ (hc.sec3_of_le I.h32 hZ hWA') hWA'

theorem cover_sp (hc : Sec3 A R T g)
    (hno : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ¬ T' ≤ A)
    (hprim : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ∀ s ∈ T', s ≠ 1 → ∀ p' ∈ A,
      s⁻¹ * p' ∈ R → ¬ D.IsPrimary p') :
    T = sec3V R T ⊓ A ∨ ∀ v ∈ sec3V R T, v ∉ A →
      ∃ x : G, rightConjugate R x ≤ sec3V R T ∧ v ∈ rightConjugate R x := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  obtain ⟨t, ht, ht1⟩ := T.bot_or_exists_ne_one.resolve_left hc.T_ne_bot
  obtain ⟨p, hp, hρ⟩ := hc.exists_aPart I.h32 I.h4 I.h34 ht
  rcases hc.case222 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy I.h222 D hq ht ht1 hp hρ with
    ⟨hle, -, h1 | h23 | h4'⟩ | hII
  · obtain ⟨⟨y, hJ⟩, ⟨p₁, y', hJ'⟩, -⟩ :=
      hc.exists_jData_pair_of_case14 I hTy D hfam hq ht ht1 hp hρ hle (Or.inl h1)
    exact hc.cover_of_jData I.h32 I.h4 I.h34 hJ hJ'
  · exact Or.inr (hc.cover_of_case23 I hTy D hfam hq ht ht1 hp hρ h23 hno hprim)
  · obtain ⟨⟨y, hJ⟩, ⟨p₁, y', hJ'⟩, -⟩ :=
      hc.exists_jData_pair_of_case14 I hTy D hfam hq ht ht1 hp hρ hle (Or.inr h4')
    exact hc.cover_of_jData I.h32 I.h4 I.h34 hJ hJ'
  · exfalso
    have := hII.2.2
    omega

theorem cover_derived_sp (hc : Sec3 A R T g)
    (hno : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ¬ T' ≤ A)
    (hprim : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ∀ s ∈ T', s ≠ 1 → ∀ p' ∈ A,
      s⁻¹ * p' ∈ R → ¬ D.IsPrimary p')
    {b : G} (hbT : rightConjugate T b ≤ centralizer (T : Set G))
    (hne : rightConjugate T b ≠ T) :
    rightConjugate T b = sec3V T (rightConjugate T b) ⊓ rightConjugate A g ∨
      ∀ v ∈ sec3V T (rightConjugate T b), v ∉ rightConjugate A g →
        ∃ y : G, rightConjugate T y ≤ sec3V T (rightConjugate T b) ∧ v ∈ rightConjugate T y := by
  have hd := hc.derived hbT hne
  have hV := sec3V_derived T g b
  have hno' : ∀ (T' : Subgroup G) (x : G), Sec3 A (rightConjugate T g⁻¹) T' x → ¬ T' ≤ A := by
    intro T' x h' hT'
    obtain ⟨k, hkK, h'', -⟩ := h'.exists_transport hc.sylowR
    have hkA : k ∈ normalizer (A : Set G) := centralizer_le_normalizer _ hkK
    exact hno _ _ h'' ((map_mono hT').trans ((rightConjugate_eq_self_iff A k).mpr hkA).le)
  have hprim' : ∀ (T' : Subgroup G) (x : G), Sec3 A (rightConjugate T g⁻¹) T' x → ∀ s ∈ T',
      s ≠ 1 → ∀ p' ∈ A, s⁻¹ * p' ∈ rightConjugate T g⁻¹ → ¬ D.IsPrimary p' := by
    intro T' x h' s hs hs1 p' hp' hρ'
    obtain ⟨k, -, h'', hpart⟩ := h'.exists_transport hc.sylowR
    refine hprim _ _ h'' (k⁻¹ * s * k) ?_ ?_ p' hp' (hpart s p' hρ' hp')
    · rw [mem_rightConjugate_iff, show k * (k⁻¹ * s * k) * k⁻¹ = s by group]
      exact hs
    · intro h
      apply hs1
      calc s = k * (k⁻¹ * s * k) * k⁻¹ := by group
        _ = 1 := by rw [h]; group
  rcases hd.cover_sp I hTy D hfam hq hno' hprim' with h1 | h2
  · left
    rw [hV] at h1
    have e1 : rightConjugate (rightConjugate T (b * g⁻¹)) g = rightConjugate T b := by
      rw [rightConjugate_mul, inv_mul_cancel_right]
    have e2 : rightConjugate (rightConjugate (sec3V T (rightConjugate T b)) g⁻¹ ⊓ A) g =
        sec3V T (rightConjugate T b) ⊓ rightConjugate A g := by
      rw [rightConjugate_inf, rightConjugate_inv_rightConjugate]
    calc rightConjugate T b = rightConjugate (rightConjugate T (b * g⁻¹)) g := e1.symm
      _ = rightConjugate (rightConjugate (sec3V T (rightConjugate T b)) g⁻¹ ⊓ A) g := by
        rw [h1]
      _ = _ := e2
  · right
    intro v hv hvA
    have hv' : g * v * g⁻¹ ∈ sec3V (rightConjugate T g⁻¹) (rightConjugate T (b * g⁻¹)) := by
      rw [hV, mem_rightConjugate_iff]
      simpa [mul_assoc] using hv
    have hvA' : g * v * g⁻¹ ∉ A := fun h => hvA ((mem_rightConjugate_iff _ _ _).mpr h)
    obtain ⟨x, hx, hvx⟩ := h2 _ hv' hvA'
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have h := (rightConjugate_le_rightConjugate_iff (x := g)).mpr hx
      rwa [hV, rightConjugate_inv_rightConjugate, rightConjugate_mul, rightConjugate_mul,
        ← mul_assoc] at h
    · rw [rightConjugate_mul, mem_rightConjugate_iff] at hvx
      rw [mem_rightConjugate_iff]
      convert hvx using 1
      group

end Config

end Sec3

end CFSG.ComponentClassification.RankTwoClassical
