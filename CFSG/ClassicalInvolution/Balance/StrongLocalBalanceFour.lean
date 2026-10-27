module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearToral

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance

section Statement

variable {K X : Type*} [Group K] [Group X]

@[expose] def ToralActionFour (ψ : K →* X) (F : Subgroup X) : Prop :=
  ∃ P : Subgroup K, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
    ∀ f ∈ F, ∃ x ∈ P, x ^ 4 = 1 ∧ ∀ y : K, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)

theorem ToralActionFour.toralAction {ψ : K →* X} {F : Subgroup X} (h : ToralActionFour ψ F) :
    ToralAction ψ F := by
  obtain ⟨P, hP, hact⟩ := h
  refine ⟨P, hP, fun f hf => ?_⟩
  obtain ⟨x, hxP, -, hxa⟩ := hact f hf
  exact ⟨x, hxP, hxa⟩

end Statement

@[expose] def StrongLocalTwoBalanceToralFourOn (t : StatedLieTag) (Q : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), Q n p e → IsFundTag t → StatedLieAdmissible t n p e →
    p ≠ 2 → 5 ≤ p ^ e →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K → ψ.range.Normal →
      ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
        (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) →
        ToralActionFour ψ F → StrongConclusion ψ.range F

theorem StrongLocalTwoBalanceToralFourOn.mono {t : StatedLieTag} {Q Q' : ℕ → ℕ → ℕ → Prop}
    (h : StrongLocalTwoBalanceToralFourOn t Q) (hQ : ∀ n p e, Q' n p e → Q n p e) :
    StrongLocalTwoBalanceToralFourOn t Q' := fun n p e hp hq => h n p e hp (hQ n p e hq)

theorem StrongLocalTwoBalanceToralOn.toFour {t : StatedLieTag} {Q : ℕ → ℕ → ℕ → Prop}
    (h : StrongLocalTwoBalanceToralOn t Q) : StrongLocalTwoBalanceToralFourOn t Q :=
  fun n p e hp hq hfund hadm hp2 h5 X _ _ ψ hker hnorm F hcard hF2 hfaith htoral =>
    h n p e hp hq hfund hadm hp2 h5 X ψ hker hnorm F hcard hF2 hfaith htoral.toralAction

namespace Linear

open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem scalar_sq_eq_one_of_pow_four {n : ℕ} {k : Type} [Field k] [NeZero n] {x : SL(n, k)}
    {r : k} (hx4 : x ^ 4 = 1)
    (hr : Matrix.scalar (Fin n) r = ((x * x : SL(n, k)) : Matrix (Fin n) (Fin n) k)) :
    r * r = 1 := by
  have h1 : ((x * x : SL(n, k)) * (x * x) : SL(n, k)) = 1 := by
    rw [← hx4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h2 := congrArg (fun z : SL(n, k) => (z : Matrix (Fin n) (Fin n) k)) h1
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h2
  rw [Matrix.SpecialLinearGroup.coe_mul] at hr
  rw [← hr, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] at h2
  have h3 := congrFun (congrFun h2 0) 0
  simpa using h3

theorem strongConclusion_gf_toral_four {p e n : ℕ} [Fact p.Prime] (hn : 3 ≤ n) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ e) (hneg : IsSquare (-1 : GaloisField p e))
    (ψ : SL(n, GaloisField p e) →* X) (hker : ψ.ker ≤ Subgroup.center SL(n, GaloisField p e))
    (hnorm : ψ.range.Normal) {F : Subgroup X} (hcard : Nat.card F = 4)
    (hF2 : ∀ f ∈ F, f * f = 1) (htoral : ToralActionFour ψ F) : StrongConclusion ψ.range F := by
  obtain ⟨P, hP, hact⟩ := htoral
  have he : e ≠ 0 := by
    rintro rfl
    simp at h5
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  have hperf := isPerfect_specialLinear (n := n) (k := GaloisField p e) (by omega) h4
  have : NeZero n := ⟨by omega⟩
  refine strongConclusion_gf_split hn hp2 h5 ψ hker hnorm hcard hF2 P hP fun f hf => ?_
  obtain ⟨x, hxP, hx4, hxa⟩ := hact f hf
  refine ⟨x, hxP, hxa, ?_⟩
  obtain ⟨r, -, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
    (mul_self_mem_center_of_lift hperf ψ hker (hF2 f hf) hxa)
  have hrr : r * r = 1 := scalar_sq_eq_one_of_pow_four hx4 hrx
  have hsq : IsSquare r := by
    have : (r - 1) * (r + 1) = 0 := by linear_combination hrr
    rcases mul_eq_zero.mp this with h | h
    · rw [sub_eq_zero.mp h]
      exact ⟨1, (mul_one 1).symm⟩
    · rw [eq_neg_of_add_eq_zero_left h]
      exact hneg
  obtain ⟨s, hs⟩ := hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hrr
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hr0 (by simpa using hs)
  refine ⟨s, hs0, ?_⟩
  have hxx : ((x * x : SL(n, GaloisField p e)) : Matrix (Fin n) (Fin n) (GaloisField p e)) =
      (x : Matrix (Fin n) (Fin n) (GaloisField p e)) * x := Matrix.SpecialLinearGroup.coe_mul _ _
  rw [← hxx, ← hrx, hs, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  simp only [pow_two]

theorem strongLocalTwoBalanceToralFourOn_PSL_neg_one :
    StrongLocalTwoBalanceToralFourOn .PSL
      (fun _ p e => ∀ _ : Fact p.Prime, IsSquare (-1 : GaloisField p e)) := by
  intro n p e hp hq hfund hadm hp2 h5 X _ _ ψ hker hnorm F hcard hF2 hfaith htoral
  have : Fact p.Prime := ⟨hp⟩
  have hneg := hq this
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases h3 : 3 ≤ m + 1
  · exact strongConclusion_gf_toral_four h3 hp2 h5 hneg ψ hker hnorm hcard hF2 htoral
  · exfalso
    obtain rfl : m = 1 := by omega
    have he : e ≠ 0 := by
      rintro rfl
      simp at h5
    have h4 : 4 ≤ Nat.card (GaloisField p e) := by
      rw [GaloisField.card p e he]
      omega
    exact false_of_toral_two (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2) h4
      ψ hker hcard hF2 hfaith htoral.toralAction

theorem isSquare_neg_one_galoisField {p e : ℕ} [Fact p.Prime] (he : e ≠ 0)
    (hq : p ^ e % 4 = 1) : IsSquare (-1 : GaloisField p e) := by
  have : Fintype (GaloisField p e) := Fintype.ofFinite _
  rw [FiniteField.isSquare_neg_one_iff, Fintype.card_eq_nat_card, GaloisField.card p e he, hq]
  norm_num

theorem strongLocalTwoBalanceToralFourOn_PSL_one_mod_four :
    StrongLocalTwoBalanceToralFourOn .PSL (fun _ p e => e ≠ 0 ∧ p ^ e % 4 = 1) :=
  strongLocalTwoBalanceToralFourOn_PSL_neg_one.mono fun _ _ _ hq _ =>
    isSquare_neg_one_galoisField hq.1 hq.2

end Linear

end CFSG.ClassicalInvolution.Balance.StrongBalance
