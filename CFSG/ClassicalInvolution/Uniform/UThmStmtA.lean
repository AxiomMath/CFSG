module

public import CFSG.ClassicalInvolution.Uniform.ULieType

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly
open scoped MatrixGroups commutatorElement

theorem three_le_iff_five_le {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h3 : p ^ f ≠ 3) :
    3 ≤ p ^ f ↔ 5 ≤ p ^ f := by
  refine ⟨fun h => ?_, fun h => by omega⟩
  by_contra hlt
  have h4 : p ^ f = 4 := by omega
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h4
  have hdvd : p ∣ 4 := by
    rw [← h4]
    exact dvd_pow_self p hf
  have : p ∣ 2 ^ 2 := by simpa using hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
    ((Fact.out : p.Prime).dvd_of_dvd_pow this))

theorem not_three_le_of_lt_five {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h3 : p ^ f ≠ 3)
    (h : ¬ 5 ≤ p ^ f) : ¬ 3 ≤ p ^ f := fun h' => h ((three_le_iff_five_le hp2 h3).mp h')

section Thm24

@[expose] def Thm4BelowU (p f : ℕ) (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ (Ω : Set (Subgroup G)),
      HypOmegaModU (.sl2 p f) Ω → classicalInvolutionOddCore G = ⊥ → (∀ K ∈ Ω, AEmpty Ω K) →
        ∀ K ∈ Ω, ∀ J ∈ Ω, (¬ ∃ g : G, conjSub g K = J) → Commutes K J

@[expose] def Thm2BelowU (p f : ℕ) (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ (Ω : Set (Subgroup G)),
      HypOmegaModU (.sl2 p f) Ω → classicalInvolutionOddCore G = ⊥ → (⨆ J ∈ Ω, J) = ⊤ → ∀ K ∈ Ω,
        (∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
          ∀ z : G, IsUniqueInvolution K z → (∃ N : Subgroup G, N.Normal ∧ IsPGroup 2 N ∧ z ∈ N) →
            K.Normal

variable {p f : ℕ} [Fact p.Prime]

theorem thm4BelowU_iff (h3 : p ^ f ≠ 3) (n : ℕ) : Thm4BelowU p f n ↔ Thm4Below p f n := by
  unfold Thm4BelowU Thm4Below
  by_cases hp2 : p = 2
  · simp [hp2]
  by_cases hq : 5 ≤ p ^ f
  · have hq3 : 3 ≤ p ^ f := by omega
    simp only [ne_eq, hp2, not_false_eq_true, hq3, hq, forall_const,
      hypOmegaModU_iff_hypOmegaMod hp2 hq]
  · simp [hp2, hq, not_three_le_of_lt_five hp2 h3 hq]

theorem thm2BelowU_iff (h3 : p ^ f ≠ 3) (n : ℕ) : Thm2BelowU p f n ↔ Thm2Below p f n := by
  unfold Thm2BelowU Thm2Below
  by_cases hp2 : p = 2
  · simp [hp2]
  by_cases hq : 5 ≤ p ^ f
  · have hq3 : 3 ≤ p ^ f := by omega
    simp only [ne_eq, hp2, not_false_eq_true, hq3, hq, forall_const,
      hypOmegaModU_iff_hypOmegaMod hp2 hq]
  · simp [hp2, hq, not_three_le_of_lt_five hp2 h3 hq]

end Thm24

section Thm5

@[expose] def Thm5BelowU (p f : ℕ) (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ Ω : Set (Subgroup G),
      HypOmegaModU (.sl2 p f) Ω → classicalInvolutionOddCore G = ⊥ →
        ∀ K ∈ Ω, ∀ J ∈ omegaNbr Ω K, ∀ z : G, IsUniqueInvolution K z →
          ∀ A : Subgroup G, IsElemAbelian2 A 2 → A ≤ K ⊔ J → z ∈ A → alphaOf A = ⊥

variable {p f : ℕ} [Fact p.Prime]

theorem thm5BelowU_iff (h3 : p ^ f ≠ 3) (n : ℕ) : Thm5BelowU p f n ↔ Thm5Below p f n := by
  unfold Thm5BelowU Thm5Below
  by_cases hp2 : p = 2
  · simp [hp2]
  by_cases hq : 5 ≤ p ^ f
  · have hq3 : 3 ≤ p ^ f := by omega
    simp only [ne_eq, hp2, not_false_eq_true, hq3, hq, forall_const,
      hypOmegaModU_iff_hypOmegaMod hp2 hq]
  · simp [hp2, hq, not_three_le_of_lt_five hp2 h3 hq]

end Thm5

section Thm3

@[expose] def Thm3CommBelowExactU (p f : ℕ) (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → classicalInvolutionOddCore G = ⊥ →
      ∀ Ω : Set (Subgroup G), HypOmegaModU (.sl2 p f) Ω → ∀ K ∈ Ω, ¬ AEmpty Ω K →
        T3.aStar Ω K = T3.vStar Ω K ∧
          ∀ L ∈ Ω, L ∉ T3.vStar Ω K → ∀ M ∈ T3.vStar Ω K, ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M

@[expose] def Thm3LieBelowExactU (p f : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → classicalInvolutionOddCore G = ⊥ →
      ∀ Ω : Set (Subgroup G), HypOmegaModU (.sl2 p f) Ω → ∀ K ∈ Ω, ¬ AEmpty Ω K →
        SectionLieTypeU p f Ω (omegaGen (T3.aStar Ω K)) .G2 0

@[expose] def Thm3TypedBelowExactU (p f : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  Thm3CommBelowExactU p f n ∧ Thm3LieBelowExactU p f n

variable {p f : ℕ} [Fact p.Prime]

theorem thm3CommBelowExactU_iff (h3 : p ^ f ≠ 3) (n : ℕ) :
    Thm3CommBelowExactU p f n ↔ T3Typed.Thm3CommBelowExact p f n := by
  unfold Thm3CommBelowExactU T3Typed.Thm3CommBelowExact
  by_cases hp2 : p = 2
  · simp [hp2]
  by_cases hq : 5 ≤ p ^ f
  · have hq3 : 3 ≤ p ^ f := by omega
    simp only [ne_eq, hp2, not_false_eq_true, hq3, hq, forall_const,
      hypOmegaModU_iff_hypOmegaMod hp2 hq]
  · simp [hp2, hq, not_three_le_of_lt_five hp2 h3 hq]

theorem thm3LieBelowExactU_iff (h3 : p ^ f ≠ 3) (n : ℕ) :
    Thm3LieBelowExactU p f n ↔ T3Typed.Thm3LieBelowExact p f n := by
  unfold Thm3LieBelowExactU T3Typed.Thm3LieBelowExact
  by_cases hp2 : p = 2
  · simp [hp2]
  by_cases hq : 5 ≤ p ^ f
  · have hq3 : 3 ≤ p ^ f := by omega
    simp only [ne_eq, hp2, not_false_eq_true, hq3, hq, forall_const,
      hypOmegaModU_iff_hypOmegaMod hp2 hq, sectionLieTypeU_iff h3]
  · simp [hp2, hq, not_three_le_of_lt_five hp2 h3 hq]

theorem thm3TypedBelowExactU_iff (h3 : p ^ f ≠ 3) (n : ℕ) :
    Thm3TypedBelowExactU p f n ↔ T3Typed.Thm3TypedBelowExact p f n := by
  unfold Thm3TypedBelowExactU T3Typed.Thm3TypedBelowExact
  rw [thm3CommBelowExactU_iff h3, thm3LieBelowExactU_iff h3]

end Thm3

end CFSG.ClassicalInvolution.Uniform
