module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec5Arith
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseDSetup

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AS76b.Sec5
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G : Type} [Group G]

variable [Finite G] {A : Subgroup G}

namespace Sec3

variable {R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem false_of_mem_isPrimary (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (h117 : ClassicalPrimaryPerfect) (D : ClassicalModel A) (hq : 4 ≤ D.q)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZ : Odd (Nat.card (center A))) {t : G} (htT : t ∈ T) (ht1 : t ≠ 1)
    (hp : D.IsPrimary t) : False := by
  have h1 := h117 G A D hc.hyp.standard.1 hZ hq t hp
  have h2 : CFSG.Quasithin.perfectCore (A ⊓ centralizer ({t} : Set G)) ≤
      admResidual (oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
        ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆) :=
    le_admResidual_of_perfect
      ((CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans le_sup_right)
      (CFSG.Quasithin.perfectCore_perfect _)
  have htg : t ∈ rightConjugate A g :=
    (Lemma39.lemma39_one h4 h32 h34 hc.hyp hc.sylowT htT ht1 hOut).1 (h2 h1)
  have h3 : t ∈ T ⊓ rightConjugate A g := mem_inf.mpr ⟨htT, htg⟩
  rw [hc.T_inf_conj hZ, mem_bot] at h3
  exact ht1 h3

theorem of_le_centralizer {x : G} (hRx : rightConjugate R x ≤ centralizer (R : Set G))
    (hne : rightConjugate R x ≠ R) : Sec3 A R (rightConjugate R x) x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hc.hyp, hc.sylowR, fun hxA => hne ?_,
    AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowR x, hRx⟩
  have hK : rightConjugate (centralizer (A : Set G)) x = centralizer (A : Set G) := by
    rw [← centralizer_rightConjugate, (rightConjugate_eq_self_iff A x).mpr hxA]
  have hRxK : rightConjugate R x ≤ centralizer (A : Set G) := hK ▸ map_mono hc.sylowR.le
  have hp : IsPGroup 2 ↥(R ⊔ rightConjugate R x) :=
    IsPGroup.to_sup_of_normal_left' hc.sylowR.isPGroup (hc.sylowR.isPGroup.map _)
      (hRx.trans (centralizer_le_normalizer _))
  have h1 : R ⊔ rightConjugate R x = R :=
    hc.sylowR.eq_of_le le_sup_left (sup_le hc.sylowR.le hRxK) hp
  exact eq_of_le_of_card_ge (le_sup_right.trans h1.le) (by rw [rightConjugate_card])

theorem exists_jData_pair_of_case14 (I : Inputs74)
    (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) (D : ClassicalModel A)
    (hfam : D.family = .symplectic) (hq : 4 ≤ D.q) {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) (hle : ∀ t' ∈ T, ∀ p' ∈ A, t'⁻¹ * p' ∈ R → p' ∈ jGroup A p)
    (hI : Case1 D p ∨ Case4 D p) :
    (∃ y, JData A R T p (jGroup A p) y) ∧
      (∃ p₁ y', JData A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p₁ (jGroup A p₁) y') ∧
      Nat.card ↥(sec3V R T ⊓ A) = D.q := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  have hZ : Odd (Nat.card (center ↥A)) :=
    (I.h222.conclusion D hq (hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)).1
  have hsyl := I.hJS.jSylowAt D hc.hyp.standard.1 hZ hq hp (hc.orderOf_aPart I.h32 ht ht1 hρ)
  obtain ⟨hreg, hcyc⟩ : RegularOn A (jGroup A p) (nonidentity (jGroup A p)) ∧
      AutCyclic A (jGroup A p) (D.q - 1) := by
    rcases hI with ⟨-, hreg, hcyc⟩ | ⟨-, hreg, hcyc⟩
    · exact ⟨hreg, hcyc⟩
    · exact ⟨hreg, hcyc⟩
  have hcardV : Nat.card ↥(sec3V R T ⊓ A) = D.q :=
    hc.card_inf_of_case14 I.h32 I.h4 I.h34 D hq ht ht1 hp hρ hle hI hsyl
  refine ⟨hc.jData_of ht ht1 hp hρ hle hreg hcyc hsyl, ?_, hcardV⟩
  have hsw := hc.swap
  obtain ⟨t₁, ht₁, ht₁1⟩ := (rightConjugate R g⁻¹).bot_or_exists_ne_one.resolve_left
    hsw.T_ne_bot
  obtain ⟨p₁, hp₁, hρ₁⟩ := hsw.exists_aPart I.h32 I.h4 I.h34 ht₁
  refine ⟨p₁, ?_⟩
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

theorem exists_jData_pair_of_typeA (I : Inputs74)
    (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) (D : ClassicalModel A)
    (hfam : D.family = .symplectic) (hq : 4 ≤ D.q) {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) {k : ℕ} (hpa : D.SuzukiType p .a k) :
    (∃ y, JData A R T p (jGroup A p) y) ∧
      (∃ p₁ y', JData A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p₁ (jGroup A p₁) y') ∧
      Nat.card ↥(sec3V R T ⊓ A) = D.q := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
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
  exact hc.exists_jData_pair_of_case14 I hTy D hfam hq ht ht1 hp hρ hle hI

theorem inf_eq_bot_or_eq_of_typeA (I : Inputs74)
    (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) (D : ClassicalModel A)
    (hfam : D.family = .symplectic) (hq : 4 ≤ D.q) {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) {k : ℕ} (hpa : D.SuzukiType p .a k) :
    T ⊓ A = ⊥ ∨ T = sec3V R T ⊓ A := by
  obtain ⟨⟨y, hJ⟩, ⟨p₁, y', hJ'⟩, -⟩ :=
    hc.exists_jData_pair_of_typeA I hTy D hfam hq ht ht1 hp hρ hpa
  exact hc.dichotomy I.h32 I.h4 I.h34 hJ hJ'

end Sec3

end CFSG.ComponentClassification.RankTwoClassical
