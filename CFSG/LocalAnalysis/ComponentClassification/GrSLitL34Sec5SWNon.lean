module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWFusModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoReal

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
  CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_inv_of_model
    {J S : Subgroup G} {hSN : S ≤ normalizer (J : Set G)} (D : WStd J S hSN) {x : MElt}
    (hx : x ∈ allM) :
    ∃ p ∈ S ⊓ J, ∃ hpJ : p ∈ J, jq J ⟨p, hpJ⟩ = nfM D.l x :=
  (D.hT0 (nfM D.l x)).1 (by
    rw [q_nfM D.hQ (lt_of_mem_allM hx)]
    exact tg_mem_T0 _ (lt_of_mem_allM hx))

theorem WStd.exists_two_eights
    {J S : Subgroup G} {hSN : S ≤ normalizer (J : Set G)}
    (D : WStd J S hSN) (hS2 : IsPGroup 2 S) :
    ∃ F₁ F₂ : Subgroup G, F₁ ≤ S ⊓ J ∧ F₂ ≤ S ⊓ J ∧ IsEightGroup F₁ ∧ IsEightGroup F₂ ∧
      F₁ ≠ F₂ := by
  have hP2 : IsPGroup 2 (S ⊓ J : Subgroup G) := hS2.to_le inf_le_left
  have hPJ : S ⊓ J ≤ J := inf_le_right
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, x₄, hx₄, hi₁, hi₂, hi₃, hi₄, h21, h12, h31, h32, h41, h42,
    h34⟩ := wFusTwoParts.two D.kb D.hkbL
  have hinv : ∀ {x : MElt} (hx : x ∈ allM) {p : G} (hp : p ∈ S ⊓ J) {hpJ : p ∈ J},
      jq J ⟨p, hpJ⟩ = nfM D.l x → isInvKB D.kb x = true → p * p = 1 ∧ p ≠ 1 := by
    intro x hx p hp hpJ hpe hi
    obtain ⟨h2, h1⟩ := (isInvKB_iff D.hQ D.hkb (lt_of_mem_allM hx)).1 hi
    refine ⟨eq_one_of_jq_eq_one hPJ hP2 (mul_mem hp hp) ?_, fun h => h1 ?_⟩
    · rw [show (⟨p * p, hPJ (mul_mem hp hp)⟩ : ↥J) = ⟨p, hpJ⟩ * ⟨p, hpJ⟩ from rfl, map_mul, hpe,
        h2]
    · rw [← hpe]
      subst h
      exact map_one (jq J)
  have hcomm : ∀ {x y : MElt} (hx : x ∈ allM) (hy : y ∈ allM) {p p' : G} (hp : p ∈ S ⊓ J)
      (hp' : p' ∈ S ⊓ J) {hpJ : p ∈ J} {hp'J : p' ∈ J}, jq J ⟨p, hpJ⟩ = nfM D.l x →
      jq J ⟨p', hp'J⟩ = nfM D.l y → (commKB D.kb x y = true ↔ p * p' = p' * p) := by
    intro x y hx hy p p' hp hp' hpJ hp'J hpe hp'e
    rw [commKB, commKB_iff D.hQ D.hkb (lt_of_mem_allM hx) (lt_of_mem_allM hy), ← hpe, ← hp'e,
      ← map_mul, ← map_mul]
    constructor
    · intro h
      exact eq_of_jq_eq hPJ hP2 (mul_mem hp hp') (mul_mem hp' hp) h
    · intro h
      congr 1
      exact Subtype.ext h
  obtain ⟨p₁, hp₁, hp₁J, hp₁e⟩ := exists_inv_of_model D hx₁
  obtain ⟨p₂, hp₂, hp₂J, hp₂e⟩ := exists_inv_of_model D hx₂
  obtain ⟨p₃, hp₃, hp₃J, hp₃e⟩ := exists_inv_of_model D hx₃
  obtain ⟨p₄, hp₄, hp₄J, hp₄e⟩ := exists_inv_of_model D hx₄
  obtain ⟨hq₁, hq₁1⟩ := hinv hx₁ hp₁ hp₁e hi₁
  obtain ⟨hq₂, hq₂1⟩ := hinv hx₂ hp₂ hp₂e hi₂
  obtain ⟨hq₃, -⟩ := hinv hx₃ hp₃ hp₃e hi₃
  obtain ⟨hq₄, -⟩ := hinv hx₄ hp₄ hp₄e hi₄
  have c12 := (hcomm hx₁ hx₂ hp₁ hp₂ hp₁e hp₂e).1 h12
  have c31 := (hcomm hx₃ hx₁ hp₃ hp₁ hp₃e hp₁e).1 h31
  have c32 := (hcomm hx₃ hx₂ hp₃ hp₂ hp₃e hp₂e).1 h32
  have c41 := (hcomm hx₄ hx₁ hp₄ hp₁ hp₄e hp₁e).1 h41
  have c42 := (hcomm hx₄ hx₂ hp₄ hp₂ hp₄e hp₂e).1 h42
  have c34 : p₃ * p₄ ≠ p₄ * p₃ := fun h => by
    have := (hcomm hx₃ hx₄ hp₃ hp₄ hp₃e hp₄e).2 h
    rw [this] at h34
    exact Bool.noConfusion h34
  have h21' : p₂ ≠ p₁ := by
    rintro rfl
    have h3 : nfM D.l x₂ = nfM D.l x₁ := by rw [← hp₁e, ← hp₂e]
    rw [← eqKB_iff D.hQ D.hkb (lt_of_mem_allM hx₂) (lt_of_mem_allM hx₁)] at h3
    rw [h3] at h21
    exact Bool.noConfusion h21
  have hp₂B : p₂ ∉ zpowers p₁ := fun h =>
    (GrS4.eq_one_or_eq_of_mem_zpowers hq₁ h).elim hq₂1 h21'
  obtain ⟨hB, hBc⟩ := GrS4.isElemTwo_sup_zpowers (isElemTwo_zpowers hq₁) hq₂ hp₂B
    (fun e he => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp he
      exact (Commute.zpow_left c12 n))
  have hcB : ∀ {t : G}, t * p₁ = p₁ * t → t * p₂ = p₂ * t →
      ∀ e ∈ zpowers p₁ ⊔ zpowers p₂, e * t = t * e := by
    intro t h1 h2 e he
    have hle : zpowers p₁ ⊔ zpowers p₂ ≤ centralizer ({t} : Set G) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h1.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h2.symm))
    exact mem_centralizer_singleton_iff.mp (hle he)
  have hp₃B : p₃ ∉ zpowers p₁ ⊔ zpowers p₂ := fun h => c34 (hcB c41 c42 p₃ h)
  have hp₄B : p₄ ∉ zpowers p₁ ⊔ zpowers p₂ := fun h => c34 (hcB c31 c32 p₄ h).symm
  obtain ⟨hF₁, hF₁c⟩ := GrS4.isElemTwo_sup_zpowers hB hq₃ hp₃B (hcB c31 c32)
  obtain ⟨hF₂, hF₂c⟩ := GrS4.isElemTwo_sup_zpowers hB hq₄ hp₄B (hcB c41 c42)
  have hcard2 : Nat.card ↥(zpowers p₁) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hq₁) hq₁1]
  have hle : ∀ {p : G}, p ∈ S ⊓ J → zpowers p₁ ⊔ zpowers p₂ ⊔ zpowers p ≤ S ⊓ J := fun hp =>
    sup_le (sup_le (zpowers_le.mpr hp₁) (zpowers_le.mpr hp₂)) (zpowers_le.mpr hp)
  refine ⟨_, _, hle hp₃, hle hp₄, ⟨hF₁, by rw [hF₁c, hBc, hcard2]⟩,
    ⟨hF₂, by rw [hF₂c, hBc, hcard2]⟩, fun heq => c34 ?_⟩
  have h3 : p₃ ∈ zpowers p₁ ⊔ zpowers p₂ ⊔ zpowers p₃ := mem_sup_right (mem_zpowers p₃)
  have h4 : p₄ ∈ zpowers p₁ ⊔ zpowers p₂ ⊔ zpowers p₃ := by
    rw [heq]
    exact mem_sup_right (mem_zpowers p₄)
  exact hF₁.1 p₃ h3 p₄ h4

theorem exists_not_isolated_of_threeConnected {S₁ : Subgroup G} (h3 : IsThreeConnected S₁)
    {F₁ F₂ : Subgroup G} (hF₁S : F₁ ≤ S₁) (hF₂S : F₂ ≤ S₁) (hF₁ : IsEightGroup F₁)
    (hF₂ : IsEightGroup F₂) (hne : F₁ ≠ F₂) {E : Subgroup G} (hES : E ≤ S₁)
    (hE : IsEightGroup E) : ∃ s ∈ S₁, s * s = 1 ∧ (∀ e ∈ E, s * e = e * s) ∧ s ∉ E := by
  by_contra hiso
  push Not at hiso
  have hinv : ∀ {B : Subgroup G}, IsAbelianTwoOfRank 3 B → (∀ x ∈ B, x * x = 1 → x ∈ E) →
      E ≤ B := by
    intro B hB hBE
    obtain ⟨F, hFB, hF, hF8⟩ := exists_isElemTwo_eight hB
    have hFE : F ≤ E := fun f hf => hBE f (hFB hf) (hF.2 f hf)
    have heq := Subgroup.eq_of_le_of_card_ge hFE (by rw [hE.2, hF8])
    rw [← heq]
    exact hFB
  have hchain : ∀ {F : Subgroup G}, Relation.ReflTransGen (fun A' B' : Subgroup G => B' ≤ S₁ ∧
      IsAbelianTwoOfRank 3 B' ∧ ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) E F →
      IsAbelianTwoOfRank 3 F ∧ ∀ x ∈ F, x * x = 1 → x ∈ E := by
    intro F hrel
    induction hrel with
    | refl => exact ⟨hE.1.isAbelianTwoOfRank hE.2.ge, fun x hx _ => hx⟩
    | tail _ hBC ih =>
      obtain ⟨hCS, hC3, hBCc⟩ := hBC
      obtain ⟨hB3, hBE⟩ := ih
      have hEB := hinv hB3 hBE
      exact ⟨hC3, fun x hx hxx => hiso x (hCS hx) hxx fun e he => (hBCc e (hEB he) x hx).symm⟩
  have heq : ∀ {F : Subgroup G}, F ≤ S₁ → IsEightGroup F → F = E := by
    intro F hFS hF
    obtain ⟨-, -, hrel⟩ := h3 E F hES hFS (hE.1.isAbelianTwoOfRank hE.2.ge)
      (hF.1.isAbelianTwoOfRank hF.2.ge)
    have hFE : F ≤ E := fun f hf => (hchain hrel).2 f hf (hF.1.2 f hf)
    exact Subgroup.eq_of_le_of_card_ge hFE (by rw [hE.2, hF.2])
  exact hne ((heq hF₁S hF₁).trans (heq hF₂S hF₂).symm)

end CFSG.ComponentClassification.GrSLit.GrS5S
