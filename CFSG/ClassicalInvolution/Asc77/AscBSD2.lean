module

public import CFSG.ClassicalInvolution.Asc77.AscBSD1
public import CFSG.ClassicalInvolution.RouteD.MultiModelSL

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD
  (ModelFund mem_modelFund_psl_iff isLongRootSL2_eq_of_involution_eq)
open scoped MatrixGroups

section Group

variable {X : Type*} [Group X]

theorem ratio_sq_eq_one {r r' : X} (hr : r * r = 1) (hr' : r' * r' = 1)
    (hc : r * r'⁻¹ ∈ Subgroup.center X) : (r * r'⁻¹) * (r * r'⁻¹) = 1 := by
  set c := r * r'⁻¹ with hc_def
  have hr'inv : r'⁻¹ = r' := inv_eq_of_mul_eq_one_right hr'
  have e : r = c * r' := by rw [hc_def, hr'inv, mul_assoc, hr', mul_one]
  have hcomm : r' * c = c * r' := Subgroup.mem_center_iff.mp hc r'
  calc c * c = c * c * (r' * r') := by rw [hr', mul_one]
    _ = c * (c * r') * r' := by group
    _ = c * (r' * c) * r' := by rw [hcomm]
    _ = (c * r') * (c * r') := by group
    _ = r * r := by rw [← e]
    _ = 1 := hr

@[expose] def CentralSqCard (X : Type*) [Group X] : Prop :=
  ∀ c₁ c₂ : X, c₁ ∈ Subgroup.center X → c₂ ∈ Subgroup.center X → c₁ * c₁ = 1 → c₂ * c₂ = 1 →
    c₁ = 1 ∨ c₂ = 1 ∨ c₁ = c₂

@[expose] def CentralSqOne (X : Type*) [Group X] : Prop :=
  ∀ c : X, c ∈ Subgroup.center X → c * c = 1 → c = 1

theorem eq_of_three_ratios (hZ : CentralSqCard X) {r₁ r₂ r₃ : X} (h₁ : r₁ * r₁ = 1)
    (h₂ : r₂ * r₂ = 1) (h₃ : r₃ * r₃ = 1) (h12 : r₁ * r₂⁻¹ ∈ Subgroup.center X)
    (h23 : r₂ * r₃⁻¹ ∈ Subgroup.center X) : r₁ = r₂ ∨ r₂ = r₃ ∨ r₁ = r₃ := by
  have e12 := ratio_sq_eq_one h₁ h₂ h12
  have e23 := ratio_sq_eq_one h₂ h₃ h23
  rcases hZ _ _ h12 h23 e12 e23 with h | h | h
  · exact Or.inl (mul_inv_eq_one.mp h)
  · exact Or.inr (Or.inl (mul_inv_eq_one.mp h))
  · refine Or.inr (Or.inr ?_)
    have hc : r₁ * r₃⁻¹ = 1 := by
      calc r₁ * r₃⁻¹ = (r₁ * r₂⁻¹) * (r₂ * r₃⁻¹) := by group
        _ = (r₂ * r₃⁻¹) * (r₂ * r₃⁻¹) := by rw [h]
        _ = 1 := e23
    exact mul_inv_eq_one.mp hc

theorem eq_of_ratio (hZ : CentralSqOne X) {r r' : X} (h₁ : r * r = 1) (h₂ : r' * r' = 1)
    (h : r * r'⁻¹ ∈ Subgroup.center X) : r = r' :=
  mul_inv_eq_one.mp (hZ _ h (ratio_sq_eq_one h₁ h₂ h))

end Group

section SL

variable {F : Type} [Field F] {n : ℕ}

theorem sl_central_sq (hn : 1 ≤ n) {c : SL(n, F)} (hc : c ∈ Subgroup.center SL(n, F))
    (hc2 : c * c = 1) :
    ∃ ω : F, ω * ω = 1 ∧ ω ^ n = 1 ∧
      Matrix.scalar (Fin n) ω = (c : Matrix (Fin n) (Fin n) F) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨ω, hω, hωc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨ω, ?_, by simpa using hω, hωc⟩
  have h1 : (Matrix.scalar (Fin n) ω) * (Matrix.scalar (Fin n) ω) = 1 := by
    rw [hωc, ← Matrix.SpecialLinearGroup.coe_mul, hc2]
    rfl
  rw [← map_mul] at h1
  have : Matrix.scalar (Fin n) (ω * ω) = Matrix.scalar (Fin n) 1 := by rw [h1, map_one]
  exact Matrix.scalar_inj.mp this

theorem sl_three_centralSqOne : CentralSqOne SL(3, F) := by
  intro c hc hc2
  obtain ⟨ω, hω2, hω3, hωc⟩ := sl_central_sq (by norm_num) hc hc2
  have hω1 : ω = 1 := by
    calc ω = ω ^ 3 := by rw [pow_succ, pow_two, hω2, one_mul]
      _ = 1 := hω3
  apply Subtype.ext
  rw [← hωc, hω1, map_one]
  rfl

theorem sl_four_centralSqCard : CentralSqCard SL(4, F) := by
  intro c₁ c₂ h₁ h₂ e₁ e₂
  obtain ⟨ω₁, hω₁, -, hc₁⟩ := sl_central_sq (by norm_num) h₁ e₁
  obtain ⟨ω₂, hω₂, -, hc₂⟩ := sl_central_sq (by norm_num) h₂ e₂
  rcases mul_self_eq_one_iff.mp hω₁ with rfl | rfl
  · left
    apply Subtype.ext
    rw [← hc₁, map_one]
    rfl
  rcases mul_self_eq_one_iff.mp hω₂ with rfl | rfl
  · right
    left
    apply Subtype.ext
    rw [← hc₂, map_one]
    rfl
  · right
    right
    apply Subtype.ext
    rw [← hc₁, ← hc₂]

theorem longRoot_eq_of_mem_inv (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} {R R' : Subgroup SL(n, F)}
    (hR : R ∈ longRootSet hn) (hR' : R' ∈ longRootSet hn) {r : SL(n, F)}
    (hr : IsInvIn R r) (hr' : IsInvIn R' r) : R = R' := by
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have e : ∀ {L : Subgroup SL(n, F)} {j : SL(n, F)}, IsLongRootSL2 hn L j → IsInvIn L r →
      r = j := by
    intro L j hj hrL
    have h2' : r ^ 2 = 1 := by simpa [pow_two] using hrL.2.1
    exact hj.eq_of_orderOf_eq_two h2 hrL.1 (orderOf_eq_prime h2' hrL.2.2)
  exact isLongRootSL2_eq_of_involution_eq h2 hi hi' ((e hi hr).symm.trans (e hi' hr'))

end SL

section Model

variable {p : ℕ} [Fact p.Prime]


theorem fund_eq_of_central_ratio_psl_three {e : ℕ} (hp2 : p ≠ 2)
    {R R' : Subgroup (modelUniv .PSL 3 p e Fact.out).K} (hR : R ∈ ModelFund p .PSL 3 e)
    (hR' : R' ∈ ModelFund p .PSL 3 e) {r r' : (modelUniv .PSL 3 p e Fact.out).K}
    (hr : IsInvIn R r) (hr' : IsInvIn R' r')
    (hc : r * r'⁻¹ ∈ Subgroup.center (modelUniv .PSL 3 p e Fact.out).K) : R = R' := by
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hrr : r = r' := eq_of_ratio sl_three_centralSqOne hr.2.1 hr'.2.1 hc
  subst hrr
  exact longRoot_eq_of_mem_inv h2 ((mem_modelFund_psl_iff (m := 2) (by norm_num) R).mp hR)
    ((mem_modelFund_psl_iff (m := 2) (by norm_num) R').mp hR') hr hr'

theorem fund_two_bound_psl_four {e : ℕ} (hp2 : p ≠ 2)
    {R₁ R₂ R₃ : Subgroup (modelUniv .PSL 4 p e Fact.out).K} (h₁ : R₁ ∈ ModelFund p .PSL 4 e)
    (h₂ : R₂ ∈ ModelFund p .PSL 4 e) (h₃ : R₃ ∈ ModelFund p .PSL 4 e)
    {r₁ r₂ r₃ : (modelUniv .PSL 4 p e Fact.out).K} (hr₁ : IsInvIn R₁ r₁) (hr₂ : IsInvIn R₂ r₂)
    (hr₃ : IsInvIn R₃ r₃)
    (h12 : r₁ * r₂⁻¹ ∈ Subgroup.center (modelUniv .PSL 4 p e Fact.out).K)
    (h23 : r₂ * r₃⁻¹ ∈ Subgroup.center (modelUniv .PSL 4 p e Fact.out).K) :
    R₁ = R₂ ∨ R₂ = R₃ ∨ R₁ = R₃ := by
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have m₁ := (mem_modelFund_psl_iff (m := 3) (by norm_num) R₁).mp h₁
  have m₂ := (mem_modelFund_psl_iff (m := 3) (by norm_num) R₂).mp h₂
  have m₃ := (mem_modelFund_psl_iff (m := 3) (by norm_num) R₃).mp h₃
  rcases eq_of_three_ratios sl_four_centralSqCard hr₁.2.1 hr₂.2.1 hr₃.2.1 h12 h23 with h | h | h
  · subst h
    exact Or.inl (longRoot_eq_of_mem_inv h2 m₁ m₂ hr₁ hr₂)
  · subst h
    exact Or.inr (Or.inl (longRoot_eq_of_mem_inv h2 m₂ m₃ hr₂ hr₃))
  · subst h
    exact Or.inr (Or.inr (longRoot_eq_of_mem_inv h2 m₁ m₃ hr₁ hr₃))

end Model

end CFSG.ClassicalInvolution.Asc77.BSC.BSD
