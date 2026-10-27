module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Abs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Cent
public import CFSG.LocalAnalysis.ComponentClassification.AS81PlaneTrans
public import CFSG.LocalAnalysis.ComponentClassification.AS81OstromWagner

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem step15_of_frame
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    (∀ e ∈ E, e ∉ A → ∃ Q ∈ pointsIn R E, e ∈ Q) ∧
      (∀ Q₁ ∈ pointsIn R E, ∀ Q₂ ∈ pointsIn R E, Q₁ ≠ Q₂ → Q₁ ⊓ Q₂ = ⊥) ∧
      Nat.card (pointsIn R E) = 16 ∧
      ∃ P₀ P : Subgroup G, P₀ ≤ normalizer (E : Set G) ∧
        normalizer (E : Set G) ≤ normalizer (P₀ : Set G) ∧
        normalizer (E : Set G) = P₀ ⊔ (normalizer (E : Set G) ⊓ normalizer (R : Set G)) ∧
        (∀ p ∈ P₀, ∀ q ∈ P₀, p * p ∈ centralizer (E : Set G) ∧
          p * q * p⁻¹ * q⁻¹ ∈ centralizer (E : Set G)) ∧
        (P₀ ⊓ centralizer (E : Set G)).relIndex P₀ = 16 ∧
        (∀ Q ∈ pointsIn R E, ∃ p ∈ P₀, rightConjugate R p = Q) ∧
        IsPGroup 2 P ∧ P ≤ P₀ ∧ P₀ = AS76b.oddCoreIn (centralizer (E : Set G)) ⊔ P ∧
        AS76b.oddCoreIn (centralizer (E : Set G)) ≤ centralizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcover, hdisj, h16, htA, -⟩ := step15_points h11 hE16 hF hL hodd
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hEA16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hF.R_le_E hF.E_le hRA1
    rw [hF.cardE, hF.cardR] at this
    omega
  have hD : PointsData R E (E ⊓ A) := by
    refine ⟨hcomm, inf_le_left, hF.R_le_E, fun Q hQ => ?_, fun e he heH => hcover e he
      fun heA => heH ⟨he, heA⟩, hdisj, fun e he => ?_, ?_, hF.elemR, hF.cardR⟩
    · rw [eq_bot_iff]
      intro x hx
      by_cases hQR : Q = R
      · subst hQR
        rw [← hRA1]
        exact ⟨hx.1, hx.2.2⟩
      · rw [← inf_eq_bot_of_mem_pointsIn_frame h11 hE16 hF hL hodd Q hQ hQR]
        exact ⟨hx.1, hx.2.2⟩
    · obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hF.R_le_E hF.E_le he
      exact ⟨a, ha, r, hr, rfl⟩
    · have hne : E ⊓ A ≠ ⊥ := fun h => by
        rw [h, card_bot] at hEA16
        omega
      obtain ⟨⟨h, hh⟩, hh1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
      exact ⟨h, hh, fun h' => hh1 (Subtype.ext h')⟩
  obtain ⟨T, hTr, hTn, hTe, hT16, hTt⟩ :=
    exists_translations h11 hE16 ostromWagnerAG24 hF hL hodd
  have hT : TranslationData R E T := ⟨h16, fun p₁ p₂ q₁ q₂ hp hq =>
    exists_pointsAction_eq_pair h11 hE16 hF hL hodd hp hq, hTr, hTn, hTe, hT16, hTt⟩
  obtain ⟨hCEO, hCcard, hOA⟩ := centralizer_eq_sup_oddCoreIn hF hL hodd
  have hXN : A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ normalizer (E : Set G) :=
    fun x hx => mem_normalizer_of_mem_inf hF hx
  have hXR : ∀ x ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G), rightConjugate R x = R :=
    fun x hx => (rightConjugate_eq_self_iff R x).mpr (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) x hx.1).symm))
  have hXt : ∀ Q₁ ∈ pointsIn R E, ∀ Q₂ ∈ pointsIn R E, Q₁ ≠ R → Q₂ ≠ R →
      ∃ x ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G), rightConjugate Q₁ x = Q₂ := by
    intro Q₁ hQ₁ Q₂ hQ₂ h₁ h₂
    obtain ⟨n₁, hn₁, rfl⟩ := htA Q₁ hQ₁ h₁
    obtain ⟨n₂, hn₂, rfl⟩ := htA Q₂ hQ₂ h₂
    refine ⟨n₁ * n₂⁻¹, mul_mem hn₁ (inv_mem hn₂), ?_⟩
    simp only [rightConjugate_mul]
    congr 1
    group
  have hOX : AS76b.oddCoreIn (centralizer (E : Set G)) ≤
      centralizer ((A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    fun o ho => mem_centralizer_iff.mpr fun x hx => mem_centralizer_iff.mp (hOA ho) x hx.1
  exact ⟨hcover, hdisj, h16, step15ii_of_data hD hT hCEO hCcard hXN hXR hXt hOX⟩

end Frame

end CFSG.ComponentClassification.AS81
