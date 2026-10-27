module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal

open Matrix
open scoped MatrixGroups

section Matrices

variable {K : Type*} [Field K]

@[expose] def upper (s : K) : SL(2, K) := ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lower (s : K) : SL(2, K) := ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def dmat (l : Kˣ) : SL(2, K) :=
  ⟨!![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

theorem upper_mulVec (s : K) (v : Fin 2 → K) :
    ((upper s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 0 + s * v 1, v 1] := by
  ext i; fin_cases i <;> simp [upper, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lower_mulVec (s : K) (v : Fin 2 → K) :
    ((lower s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 0, s * v 0 + v 1] := by
  ext i; fin_cases i <;> simp [lower, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem dmat_mulVec (l : Kˣ) (v : Fin 2 → K) :
    ((dmat l : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      ![(l : K) * v 0, ((l⁻¹ : Kˣ) : K) * v 1] := by
  ext i; fin_cases i <;> simp [dmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem upper_mul_upper (s s' : K) : upper s * upper s' = upper (s + s') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upper_zero : upper (0 : K) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [upper]

theorem dmat_mul_dmat (l l' : Kˣ) : dmat l * dmat l' = dmat (l * l') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j; fin_cases i <;> fin_cases j <;> simp [dmat, Matrix.mul_apply, Fin.sum_univ_two,
    mul_comm]

theorem dmat_conj_upper (l : Kˣ) (s : K) :
    dmat l * upper s * (dmat l)⁻¹ = upper ((l : K) ^ 2 * s) := by
  have hinv : (dmat l)⁻¹ = dmat l⁻¹ := by
    rw [eq_comm, eq_inv_iff_mul_eq_one, dmat_mul_dmat, inv_mul_cancel]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [dmat]
  rw [hinv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j; fin_cases i <;> fin_cases j <;> simp [dmat, upper, Matrix.mul_apply, Fin.sum_univ_two]
  ring

omit [Field K] in
theorem vec_eq (v : Fin 2 → K) : v = ![v 0, v 1] := by
  ext i; fin_cases i <;> rfl

theorem exists_SL_mulVec_e₁ {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ B : SL(2, K), (B : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (by ext i; fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by simp [Matrix.det_fin_two, h1]⟩, ?_⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [Matrix.det_fin_two, h0]⟩, ?_⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_SL_mulVec_eq {v w : Fin 2 → K} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ B : SL(2, K), (B : Matrix (Fin 2) (Fin 2) K) *ᵥ v = w := by
  obtain ⟨B, hB⟩ := exists_SL_mulVec_e₁ hv
  obtain ⟨C, hC⟩ := exists_SL_mulVec_e₁ hw
  refine ⟨C * B⁻¹, ?_⟩
  rw [← hB, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right, hC]

end Matrices

section Forms

variable {K : Type*} [Field K]

theorem scalar_bilin_eq_zero [Finite K] [CharP K 2] (γ : K → K → K)
    (hadd₁ : ∀ a a' b, γ (a + a') b = γ a b + γ a' b)
    (hadd₂ : ∀ a b b', γ a (b + b') = γ a b + γ a b')
    (hhom : ∀ l : K, l ≠ 0 → ∀ a b, γ (l * a) (l * b) = l * γ a b)
    (halt : ∀ a, γ a a = 0) : ∀ a b, γ a b = 0 := by
  have h0₁ : ∀ b, γ 0 b = 0 := fun b => by
    have := hadd₁ 0 0 b
    rw [add_zero] at this
    exact left_eq_add.mp this
  have h0₂ : ∀ a, γ a 0 = 0 := fun a => by
    have := hadd₂ a 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hsq : ∀ x : K, γ (x * x) 1 = 0 := by
    intro x
    by_cases hx0 : x = 0
    · rw [hx0, mul_zero, h0₁]
    by_cases hx1 : x = 1
    · rw [hx1, mul_one, halt]
    have hx1' : x + 1 ≠ 0 := by
      intro h
      apply hx1
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h - h2
    have e1 : γ ((x + 1) * x) ((x + 1) * 1) = (x + 1) * γ x 1 := hhom _ hx1' x 1
    have e2 : γ (x * x) (x * 1) = x * γ x 1 := hhom _ hx0 x 1
    have e3 : γ ((x + 1) * x) ((x + 1) * 1) =
        γ (x * x) (x * 1) + γ (x * x) 1 + γ x x + γ x 1 := by
      rw [add_mul, one_mul, mul_one, hadd₁, hadd₂, hadd₂, mul_one]
      ring
    rw [e1, e2, halt] at e3
    linear_combination -e3
  have h1 : ∀ a, γ a 1 = 0 := fun a => by
    obtain ⟨r, rfl⟩ := isSquare_of_charTwo' a
    exact hsq r
  intro a b
  by_cases hb : b = 0
  · rw [hb, h0₂]
  have := hhom b hb (a / b) 1
  rw [mul_div_cancel₀ a hb, mul_one, h1, mul_zero] at this
  exact this

theorem pair_eq_zero [Finite K] [CharP K 2] (c : (Fin 2 → K) → (Fin 2 → K) → (Fin 2 → K))
    (hadd₁ : ∀ ξ ξ' η, c (ξ + ξ') η = c ξ η + c ξ' η)
    (hadd₂ : ∀ ξ η η', c ξ (η + η') = c ξ η + c ξ η')
    (halt : ∀ ξ, c ξ ξ = 0)
    (hequiv : ∀ (B : SL(2, K)) ξ η, c ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ ξ)
      ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ η) = (B : Matrix (Fin 2) (Fin 2) K) *ᵥ c ξ η) :
    ∀ ξ η, c ξ η = 0 := by
  have hanti : ∀ ξ η, c η ξ = -c ξ η := fun ξ η => by
    have h := halt (ξ + η)
    rw [hadd₁, hadd₂, hadd₂, halt, halt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  have hv : ∀ a b : K, ![a, 0] + ![b, 0] = ![a + b, 0] := fun a b => by
    ext i; fin_cases i <;> simp
  have hv' : ∀ a b : K, ![0, a] + ![0, b] = ![0, a + b] := fun a b => by
    ext i; fin_cases i <;> simp
  have h1 : ∀ a b : K, c ![a, 0] ![b, 0] = 0 := by
    have hfix : ∀ a b : K, (c ![a, 0] ![b, 0]) 1 = 0 := fun a b => by
      have h := congrFun (hequiv (upper 1) ![a, 0] ![b, 0]) 0
      rw [upper_mulVec, upper_mulVec, upper_mulVec] at h
      simpa using h
    have hγ := scalar_bilin_eq_zero (fun a b => (c ![a, 0] ![b, 0]) 0)
      (fun a a' b => by rw [← hv, hadd₁, Pi.add_apply])
      (fun a b b' => by rw [← hv, hadd₂, Pi.add_apply])
      (fun l hl a b => by
        have h := congrFun (hequiv (dmat (Units.mk0 l hl)) ![a, 0] ![b, 0]) 0
        rw [dmat_mulVec, dmat_mulVec, dmat_mulVec] at h
        simpa using h)
      (fun a => by rw [halt]; rfl)
    intro a b
    rw [vec_eq (c ![a, 0] ![b, 0]), hγ, hfix]
    ext i; fin_cases i <;> rfl
  have h2 : ∀ a b : K, c ![0, a] ![0, b] = 0 := by
    have hfix : ∀ a b : K, (c ![0, a] ![0, b]) 0 = 0 := fun a b => by
      have h := congrFun (hequiv (lower 1) ![0, a] ![0, b]) 1
      rw [lower_mulVec, lower_mulVec, lower_mulVec] at h
      simpa using h
    have hγ := scalar_bilin_eq_zero (fun a b => (c ![0, a] ![0, b]) 1)
      (fun a a' b => by rw [← hv', hadd₁, Pi.add_apply])
      (fun a b b' => by rw [← hv', hadd₂, Pi.add_apply])
      (fun l hl a b => by
        have h := congrFun (hequiv (dmat (Units.mk0 l hl)⁻¹) ![0, a] ![0, b]) 1
        rw [dmat_mulVec, dmat_mulVec, dmat_mulVec] at h
        simpa using h)
      (fun a => by rw [halt]; rfl)
    intro a b
    rw [vec_eq (c ![0, a] ![0, b]), hγ, hfix]
    ext i; fin_cases i <;> rfl
  have h12 : ∀ a b : K, c ![a, 0] ![0, b] = 0 := by
    intro a b
    have hA := congrFun (hequiv (upper 1) ![a, 0] ![0, b]) 0
    have hB := congrFun (hequiv (lower 1) ![a, 0] ![0, b]) 1
    have e1 : ((upper (1 : K) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![0, b] =
        ![0, b] + ![b, 0] := by
      rw [upper_mulVec]; ext i; fin_cases i <;> simp
    have e2 : ((lower (1 : K) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![a, 0] =
        ![a, 0] + ![0, a] := by
      rw [lower_mulVec]; ext i; fin_cases i <;> simp
    have e3 : ((upper (1 : K) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![a, 0] = ![a, 0] := by
      rw [upper_mulVec]; ext i; fin_cases i <;> simp
    have e4 : ((lower (1 : K) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![0, b] = ![0, b] := by
      rw [lower_mulVec]; ext i; fin_cases i <;> simp
    rw [e1, e3, hadd₂, h1, add_zero, upper_mulVec] at hA
    rw [e2, e4, hadd₁, h2, add_zero, lower_mulVec] at hB
    simp at hA hB
    rw [vec_eq (c ![a, 0] ![0, b]), hA, hB]
    ext i; fin_cases i <;> rfl
  intro ξ η
  have hξ : ξ = ![ξ 0, 0] + ![0, ξ 1] := by
    ext i; fin_cases i <;> simp
  have hη : η = ![η 0, 0] + ![0, η 1] := by
    ext i; fin_cases i <;> simp
  rw [hξ, hη, hadd₁, hadd₂, hadd₂, h1, h12, hanti ![η 0, 0], h12, h2]
  simp

theorem exists_unit_cube_ne_one [Finite K] (hK : 8 ≤ Nat.card K) :
    ∃ l : Kˣ, (l : K) ^ 3 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hle : (⊤ : Subgroup Kˣ) ≤ rootsOfUnity 3 K := fun l _ => by
    rw [mem_rootsOfUnity]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hcon l, Units.val_one])
  have h1 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_top] at h1
  have h2 := card_rootsOfUnity K 3
  have h3 := Nat.card_units K
  omega

end Forms

structure WSetting (G : Type*) [Group G] (K : Type*) [Field K] where
  W : Subgroup G
  ι : (Fin 2 → K) → G
  ψ : G → Fin 2 → K
  lev : SL(2, K) →* G
  tor : Kˣ →* G
  ι_add : ∀ u v, ι (u + v) = ι u * ι v
  ι_injective : Function.Injective ι
  ι_mem : ∀ v, ι v ∈ W
  ι_comm : ∀ v, ∀ a ∈ W, ι v * a = a * ι v
  comm_mem : ∀ a ∈ W, ∀ b ∈ W, ∃ v, a * b * a⁻¹ * b⁻¹ = ι v
  ψ_mul : ∀ a ∈ W, ∀ b ∈ W, ψ (a * b) = ψ a + ψ b
  ψ_surj : ∀ ξ, ∃ a ∈ W, ψ a = ξ
  ψ_eq_zero : ∀ a ∈ W, ψ a = 0 → ∃ v, ι v = a
  ψ_ι : ∀ v, ψ (ι v) = 0
  lev_mem : ∀ B, ∀ a ∈ W, lev B * a * (lev B)⁻¹ ∈ W
  lev_ψ : ∀ B, ∀ a ∈ W, ψ (lev B * a * (lev B)⁻¹) = (B : Matrix (Fin 2) (Fin 2) K) *ᵥ ψ a
  lev_ι : ∀ B v, lev B * ι v * (lev B)⁻¹ = ι ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ v)
  tor_mem : ∀ l, ∀ a ∈ W, tor l * a * (tor l)⁻¹ ∈ W
  tor_ψ : ∀ l, ∀ a ∈ W, ψ (tor l * a * (tor l)⁻¹) = ((l : K) ^ 3) • ψ a
  tor_ι : ∀ l v, tor l * ι v * (tor l)⁻¹ = ι (((l : K) ^ 3) • v)
  tor_lev : ∀ l B, tor l * lev B = lev B * tor l

namespace WSetting

variable {G : Type*} [Group G] {K : Type*} [Field K] (S : WSetting G K)

theorem ι_zero : S.ι 0 = 1 := by
  have h := S.ι_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem ι_neg (v : Fin 2 → K) : S.ι (-v) = (S.ι v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← S.ι_add, neg_add_cancel, S.ι_zero]

theorem ψ_one : S.ψ 1 = 0 := by
  have h := S.ψ_mul 1 (one_mem _) 1 (one_mem _)
  rw [one_mul] at h
  exact left_eq_add.mp h

theorem ψ_inv {a : G} (ha : a ∈ S.W) : S.ψ a⁻¹ = -S.ψ a := by
  have h := S.ψ_mul a ha a⁻¹ (inv_mem ha)
  rw [mul_inv_cancel, S.ψ_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem exists_eq_mul_ι {a b : G} (ha : a ∈ S.W) (hb : b ∈ S.W) (h : S.ψ a = S.ψ b) :
    ∃ v, a = b * S.ι v := by
  obtain ⟨v, hv⟩ := S.ψ_eq_zero (b⁻¹ * a) (mul_mem (inv_mem hb) ha) (by
    rw [S.ψ_mul _ (inv_mem hb) _ ha, S.ψ_inv hb, h, neg_add_cancel])
  exact ⟨v, by rw [hv, mul_inv_cancel_left]⟩

noncomputable def sec (ξ : Fin 2 → K) : G := Classical.choose (S.ψ_surj ξ)

theorem sec_mem (ξ : Fin 2 → K) : S.sec ξ ∈ S.W := (Classical.choose_spec (S.ψ_surj ξ)).1

theorem ψ_sec (ξ : Fin 2 → K) : S.ψ (S.sec ξ) = ξ := (Classical.choose_spec (S.ψ_surj ξ)).2

theorem commutator_mul_ι {a b : G} (ha : a ∈ S.W) (hb : b ∈ S.W) (v v' : Fin 2 → K) :
    a * S.ι v * (b * S.ι v') * (a * S.ι v)⁻¹ * (b * S.ι v')⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h1 : S.ι v * (b * S.ι v') = (b * S.ι v') * S.ι v :=
    S.ι_comm v _ (mul_mem hb (S.ι_mem v'))
  have h2 : S.ι v' * a⁻¹ = a⁻¹ * S.ι v' := S.ι_comm v' _ (inv_mem ha)
  calc a * S.ι v * (b * S.ι v') * (a * S.ι v)⁻¹ * (b * S.ι v')⁻¹
      = a * (S.ι v * (b * S.ι v')) * (S.ι v)⁻¹ * a⁻¹ * (S.ι v')⁻¹ * b⁻¹ := by group
    _ = a * b * (S.ι v' * a⁻¹) * (S.ι v')⁻¹ * b⁻¹ := by rw [h1]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2]; group

noncomputable def pair (ξ η : Fin 2 → K) : Fin 2 → K :=
  Classical.choose (S.comm_mem _ (S.sec_mem ξ) _ (S.sec_mem η))

theorem ι_pair (ξ η : Fin 2 → K) :
    S.ι (S.pair ξ η) = S.sec ξ * S.sec η * (S.sec ξ)⁻¹ * (S.sec η)⁻¹ :=
  (Classical.choose_spec (S.comm_mem _ (S.sec_mem ξ) _ (S.sec_mem η))).symm

theorem commutator_eq {a b : G} (ha : a ∈ S.W) (hb : b ∈ S.W) :
    a * b * a⁻¹ * b⁻¹ = S.ι (S.pair (S.ψ a) (S.ψ b)) := by
  obtain ⟨v, hv⟩ := S.exists_eq_mul_ι ha (S.sec_mem (S.ψ a)) (S.ψ_sec _).symm
  obtain ⟨v', hv'⟩ := S.exists_eq_mul_ι hb (S.sec_mem (S.ψ b)) (S.ψ_sec _).symm
  rw [S.ι_pair]
  calc a * b * a⁻¹ * b⁻¹ = S.sec (S.ψ a) * S.ι v * (S.sec (S.ψ b) * S.ι v') *
        (S.sec (S.ψ a) * S.ι v)⁻¹ * (S.sec (S.ψ b) * S.ι v')⁻¹ := by rw [← hv, ← hv']
    _ = _ := S.commutator_mul_ι (S.sec_mem _) (S.sec_mem _) v v'

theorem commutator_comm {a b c : G} (ha : a ∈ S.W) (hb : b ∈ S.W) (hc : c ∈ S.W) :
    c * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * c := by
  rw [S.commutator_eq ha hb]
  exact (S.ι_comm _ c hc).symm

theorem pair_add_left (ξ ξ' η : Fin 2 → K) :
    S.pair (ξ + ξ') η = S.pair ξ η + S.pair ξ' η := by
  set a := S.sec ξ
  set a' := S.sec ξ'
  set b := S.sec η
  have ha := S.sec_mem ξ
  have ha' := S.sec_mem ξ'
  have hb := S.sec_mem η
  have h := S.commutator_eq (mul_mem ha ha') hb
  rw [S.ψ_mul _ ha _ ha', S.ψ_sec, S.ψ_sec, S.ψ_sec] at h
  have e : a * a' * b * (a * a')⁻¹ * b⁻¹ =
      (a * (a' * b * a'⁻¹ * b⁻¹) * a⁻¹) * (a * b * a⁻¹ * b⁻¹) := by group
  have hc : a * (a' * b * a'⁻¹ * b⁻¹) * a⁻¹ = a' * b * a'⁻¹ * b⁻¹ := by
    rw [S.commutator_comm ha' hb ha, mul_inv_cancel_right]
  rw [e, hc, S.commutator_eq ha' hb, S.commutator_eq ha hb, S.ψ_sec, S.ψ_sec, S.ψ_sec,
    ← S.ι_add] at h
  rw [← S.ι_injective h, add_comm]

theorem pair_add_right (ξ η η' : Fin 2 → K) :
    S.pair ξ (η + η') = S.pair ξ η + S.pair ξ η' := by
  set a := S.sec ξ
  set b := S.sec η
  set b' := S.sec η'
  have ha := S.sec_mem ξ
  have hb := S.sec_mem η
  have hb' := S.sec_mem η'
  have h := S.commutator_eq ha (mul_mem hb hb')
  rw [S.ψ_mul _ hb _ hb', S.ψ_sec, S.ψ_sec, S.ψ_sec] at h
  have e : a * (b * b') * a⁻¹ * (b * b')⁻¹ =
      (a * b * a⁻¹ * b⁻¹) * (b * (a * b' * a⁻¹ * b'⁻¹) * b⁻¹) := by group
  have hc : b * (a * b' * a⁻¹ * b'⁻¹) * b⁻¹ = a * b' * a⁻¹ * b'⁻¹ := by
    rw [S.commutator_comm ha hb' hb, mul_inv_cancel_right]
  rw [e, hc, S.commutator_eq ha hb, S.commutator_eq ha hb', S.ψ_sec, S.ψ_sec, S.ψ_sec,
    ← S.ι_add] at h
  exact (S.ι_injective h).symm

theorem pair_self (ξ : Fin 2 → K) : S.pair ξ ξ = 0 := by
  have h := S.commutator_eq (S.sec_mem ξ) (S.sec_mem ξ)
  rw [mul_inv_cancel_right, mul_inv_cancel, S.ψ_sec, ← S.ι_zero] at h
  exact S.ι_injective h.symm

theorem pair_equiv (B : SL(2, K)) (ξ η : Fin 2 → K) :
    S.pair ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ ξ) ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ η) =
      (B : Matrix (Fin 2) (Fin 2) K) *ᵥ S.pair ξ η := by
  set a := S.sec ξ
  set b := S.sec η
  have ha := S.sec_mem ξ
  have hb := S.sec_mem η
  have h := S.commutator_eq (S.lev_mem B a ha) (S.lev_mem B b hb)
  rw [S.lev_ψ B a ha, S.lev_ψ B b hb, S.ψ_sec, S.ψ_sec] at h
  have e : S.lev B * a * (S.lev B)⁻¹ * (S.lev B * b * (S.lev B)⁻¹) *
      (S.lev B * a * (S.lev B)⁻¹)⁻¹ * (S.lev B * b * (S.lev B)⁻¹)⁻¹ =
      S.lev B * (a * b * a⁻¹ * b⁻¹) * (S.lev B)⁻¹ := by group
  rw [e, S.commutator_eq ha hb, S.ψ_sec, S.ψ_sec, S.lev_ι] at h
  exact (S.ι_injective h).symm

theorem comm [Finite K] [CharP K 2] {a b : G} (ha : a ∈ S.W) (hb : b ∈ S.W) : a * b = b * a := by
  have h := S.commutator_eq ha hb
  rw [pair_eq_zero S.pair S.pair_add_left S.pair_add_right S.pair_self S.pair_equiv,
    S.ι_zero] at h
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h, one_mul]

end WSetting

structure XSetting (G : Type*) [Group G] (K : Type*) [Field K] where
  X : Subgroup G
  t : G
  ι : (Fin 2 → K) → G
  lev : SL(2, K) →* G
  tor : Kˣ →* G
  ι_add : ∀ u v, ι (u + v) = ι u * ι v
  ι_injective : Function.Injective ι
  ι_mem : ∀ v, ι v ∈ X
  ι_comm : ∀ v, ∀ x ∈ X, ι v * x = x * ι v
  t_mem : t ∈ X
  t_mul_self : t * t = 1
  comm_mem : ∀ x ∈ X, ∃ v, t * x * t * x⁻¹ = ι v
  comm_surj : ∀ v, ∃ x ∈ X, t * x * t * x⁻¹ = ι v
  comm_eq_one : ∀ x ∈ X, t * x * t * x⁻¹ = 1 → ∃ v, x = ι v ∨ x = ι v * t
  lev_mem : ∀ B, ∀ x ∈ X, lev B * x * (lev B)⁻¹ ∈ X
  lev_t : ∀ B, lev B * t = t * lev B
  lev_ι : ∀ B v, lev B * ι v * (lev B)⁻¹ = ι ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ v)
  tor_mem : ∀ l, ∀ x ∈ X, tor l * x * (tor l)⁻¹ ∈ X
  tor_t : ∀ l, tor l * t = t * tor l
  tor_ι : ∀ l v, tor l * ι v * (tor l)⁻¹ = ι (((l : K) ^ 3) • v)
  tor_lev : ∀ l B, tor l * lev B = lev B * tor l

namespace XSetting

variable {G : Type*} [Group G] {K : Type*} [Field K] (S : XSetting G K)

theorem ι_zero : S.ι 0 = 1 := by
  have h := S.ι_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem ι_neg (v : Fin 2 → K) : S.ι (-v) = (S.ι v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← S.ι_add, neg_add_cancel, S.ι_zero]

theorem t_inv : S.t⁻¹ = S.t := inv_eq_of_mul_eq_one_right S.t_mul_self

theorem ι_comm_t (v : Fin 2 → K) : S.ι v * S.t = S.t * S.ι v := S.ι_comm v _ S.t_mem

noncomputable def ψ (x : G) : Fin 2 → K := Classical.epsilon fun v => S.t * x * S.t * x⁻¹ = S.ι v

theorem ι_ψ {x : G} (hx : x ∈ S.X) : S.ι (S.ψ x) = S.t * x * S.t * x⁻¹ :=
  (Classical.epsilon_spec (S.comm_mem x hx)).symm

theorem ψ_mul {x y : G} (hx : x ∈ S.X) (hy : y ∈ S.X) : S.ψ (x * y) = S.ψ x + S.ψ y := by
  apply S.ι_injective
  rw [S.ι_add, S.ι_ψ (mul_mem hx hy), S.ι_ψ hx]
  have h : x * S.ι (S.ψ y) * x⁻¹ = S.ι (S.ψ y) := by
    rw [← S.ι_comm _ x hx, mul_inv_cancel_right]
  calc S.t * (x * y) * S.t * (x * y)⁻¹ = S.t * x * S.t * x⁻¹ *
      (x * (S.t * y * S.t * y⁻¹) * x⁻¹) := by
        rw [show S.t * x * S.t * x⁻¹ * (x * (S.t * y * S.t * y⁻¹) * x⁻¹) =
          S.t * x * (S.t * S.t) * y * S.t * y⁻¹ * x⁻¹ by group, S.t_mul_self]
        group
    _ = S.t * x * S.t * x⁻¹ * S.ι (S.ψ y) := by rw [← S.ι_ψ hy, h]

theorem ψ_one : S.ψ 1 = 0 := by
  have h := S.ψ_mul (one_mem S.X) (one_mem S.X)
  rw [one_mul] at h
  exact left_eq_add.mp h

theorem ψ_inv {x : G} (hx : x ∈ S.X) : S.ψ x⁻¹ = -S.ψ x := by
  have h := S.ψ_mul hx (inv_mem hx)
  rw [mul_inv_cancel, S.ψ_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem ψ_eq_zero_iff {x : G} (hx : x ∈ S.X) : S.ψ x = 0 ↔ S.t * x * S.t * x⁻¹ = 1 := by
  rw [← S.ι_ψ hx, ← S.ι_zero]
  exact S.ι_injective.eq_iff.symm

theorem ψ_ι (v : Fin 2 → K) : S.ψ (S.ι v) = 0 := by
  rw [S.ψ_eq_zero_iff (S.ι_mem v), ← S.ι_comm_t, mul_assoc (S.ι v), S.t_mul_self, mul_one,
    mul_inv_cancel]

theorem ψ_t : S.ψ S.t = 0 := by
  rw [S.ψ_eq_zero_iff S.t_mem, S.t_mul_self, one_mul, mul_inv_cancel]

theorem ψ_surj (v : Fin 2 → K) : ∃ x ∈ S.X, S.ψ x = v := by
  obtain ⟨x, hx, hxv⟩ := S.comm_surj v
  exact ⟨x, hx, S.ι_injective (by rw [S.ι_ψ hx, hxv])⟩

theorem exists_of_ψ_eq_zero {x : G} (hx : x ∈ S.X) (h : S.ψ x = 0) :
    ∃ v, x = S.ι v ∨ x = S.ι v * S.t :=
  S.comm_eq_one x hx ((S.ψ_eq_zero_iff hx).mp h)

theorem ι_ψ_conj {g x : G} (hx : x ∈ S.X) (hgx : g * x * g⁻¹ ∈ S.X) (hgt : g * S.t = S.t * g) :
    S.ι (S.ψ (g * x * g⁻¹)) = g * S.ι (S.ψ x) * g⁻¹ := by
  rw [S.ι_ψ hgx, S.ι_ψ hx]
  have h : g * S.t * g⁻¹ = S.t := by rw [hgt, mul_inv_cancel_right]
  calc S.t * (g * x * g⁻¹) * S.t * (g * x * g⁻¹)⁻¹ =
      (g * S.t * g⁻¹) * (g * x * g⁻¹) * (g * S.t * g⁻¹) * (g * x * g⁻¹)⁻¹ := by rw [h]
    _ = g * (S.t * x * S.t * x⁻¹) * g⁻¹ := by group

theorem ψ_lev {x : G} (hx : x ∈ S.X) (B : SL(2, K)) :
    S.ψ (S.lev B * x * (S.lev B)⁻¹) = (B : Matrix (Fin 2) (Fin 2) K) *ᵥ S.ψ x := by
  apply S.ι_injective
  rw [S.ι_ψ_conj hx (S.lev_mem B x hx) (S.lev_t B), S.lev_ι]

theorem ψ_tor {x : G} (hx : x ∈ S.X) (l : Kˣ) :
    S.ψ (S.tor l * x * (S.tor l)⁻¹) = ((l : K) ^ 3) • S.ψ x := by
  apply S.ι_injective
  rw [S.ι_ψ_conj hx (S.tor_mem l x hx) (S.tor_t l), S.tor_ι]

theorem t_ne_ι (v : Fin 2 → K) : S.t ≠ S.ι v := by
  intro h
  have he₁ : (![1, 0] : Fin 2 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  obtain ⟨x, hx, hxv⟩ := S.comm_surj ![1, 0]
  apply he₁
  apply S.ι_injective
  rw [← hxv, S.ι_zero, h, S.ι_comm v x hx, mul_assoc x, ← h, S.t_mul_self, mul_one,
    mul_inv_cancel]

def InV (a : G) : Prop := ∃ v, S.ι v = a

def InE (a : G) : Prop := a ∈ S.X ∧ S.ψ a = 0

noncomputable def par (a : G) : ZMod 2 := @ite _ (S.InV a) (Classical.propDecidable _) 0 1

theorem par_of_inV {a : G} (h : S.InV a) : S.par a = 0 := by
  simp only [par, h, ite_true]

theorem par_of_not_inV {a : G} (h : ¬ S.InV a) : S.par a = 1 := by
  simp only [par, h, ite_false]

theorem inV_of_par {a : G} (h : S.par a = 0) : S.InV a := by
  by_contra hn
  rw [S.par_of_not_inV hn] at h
  exact one_ne_zero h

theorem not_inV_mul_t (v : Fin 2 → K) : ¬ S.InV (S.ι v * S.t) := by
  rintro ⟨w, hw⟩
  apply S.t_ne_ι (-v + w)
  rw [S.ι_add, S.ι_neg, hw, inv_mul_cancel_left]

theorem InE.mul {S : XSetting G K} {a b : G} (ha : S.InE a) (hb : S.InE b) : S.InE (a * b) :=
  ⟨mul_mem ha.1 hb.1, by rw [S.ψ_mul ha.1 hb.1, ha.2, hb.2, add_zero]⟩

theorem InE.conj {S : XSetting G K} {a x : G} (ha : S.InE a) (hx : x ∈ S.X) :
    S.InE (x * a * x⁻¹) :=
  ⟨mul_mem (mul_mem hx ha.1) (inv_mem hx), by
    rw [S.ψ_mul (mul_mem hx ha.1) (inv_mem hx), S.ψ_mul hx ha.1, S.ψ_inv hx, ha.2, add_zero,
      add_neg_cancel]⟩

theorem inE_mul_self {x : G} (hx : x ∈ S.X) [CharP K 2] : S.InE (x * x) :=
  ⟨mul_mem hx hx, by rw [S.ψ_mul hx hx]; funext i; exact CharTwo.add_self_eq_zero _⟩

theorem inE_comm {x y : G} (hx : x ∈ S.X) (hy : y ∈ S.X) : S.InE (x⁻¹ * y * x * y⁻¹) := by
  refine ⟨mul_mem (mul_mem (mul_mem (inv_mem hx) hy) hx) (inv_mem hy), ?_⟩
  rw [S.ψ_mul (mul_mem (mul_mem (inv_mem hx) hy) hx) (inv_mem hy),
    S.ψ_mul (mul_mem (inv_mem hx) hy) hx, S.ψ_mul (inv_mem hx) hy, S.ψ_inv hx, S.ψ_inv hy]
  abel

theorem par_mul {a b : G} (ha : S.InE a) (hb : S.InE b) : S.par (a * b) = S.par a + S.par b := by
  obtain ⟨v, rfl | rfl⟩ := S.exists_of_ψ_eq_zero ha.1 ha.2 <;>
    obtain ⟨v', rfl | rfl⟩ := S.exists_of_ψ_eq_zero hb.1 hb.2
  · rw [S.par_of_inV ⟨v, rfl⟩, S.par_of_inV ⟨v', rfl⟩, S.par_of_inV ⟨v + v', S.ι_add v v'⟩,
      add_zero]
  · rw [S.par_of_inV ⟨v, rfl⟩, S.par_of_not_inV (S.not_inV_mul_t v'), ← mul_assoc, ← S.ι_add,
      S.par_of_not_inV (S.not_inV_mul_t _), zero_add]
  · rw [S.par_of_not_inV (S.not_inV_mul_t v), S.par_of_inV ⟨v', rfl⟩, mul_assoc,
      ← S.ι_comm_t, ← mul_assoc, ← S.ι_add, S.par_of_not_inV (S.not_inV_mul_t _), add_zero]
  · rw [S.par_of_not_inV (S.not_inV_mul_t v), S.par_of_not_inV (S.not_inV_mul_t v')]
    have e : S.ι v * S.t * (S.ι v' * S.t) = S.ι (v + v') := by
      rw [S.ι_add, mul_assoc, ← mul_assoc S.t, ← S.ι_comm_t, mul_assoc, S.t_mul_self, mul_one]
    rw [e, S.par_of_inV ⟨_, rfl⟩]
    decide

theorem par_conj {a x : G} (hx : x ∈ S.X) : S.par (x * a * x⁻¹) = S.par a := by
  have h : S.InV (x * a * x⁻¹) ↔ S.InV a := by
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨w, ?_⟩
      calc S.ι w = x⁻¹ * (x * S.ι w) := by group
        _ = x⁻¹ * (S.ι w * x) := by rw [S.ι_comm w x hx]
        _ = a := by rw [hw]; group
    · rintro ⟨w, rfl⟩
      exact ⟨w, by rw [← S.ι_comm w x hx, mul_inv_cancel_right]⟩
  by_cases ha : S.InV a
  · rw [S.par_of_inV ha, S.par_of_inV (h.mpr ha)]
  · rw [S.par_of_not_inV ha, S.par_of_not_inV (fun h' => ha (h.mp h'))]

theorem par_lev (a : G) (B : SL(2, K)) : S.par (S.lev B * a * (S.lev B)⁻¹) = S.par a := by
  have h : S.InV (S.lev B * a * (S.lev B)⁻¹) ↔ S.InV a := by
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ w, ?_⟩
      rw [← S.lev_ι, hw, map_inv, inv_inv]
      group
    · rintro ⟨w, rfl⟩
      exact ⟨_, (S.lev_ι B w).symm⟩
  by_cases ha : S.InV a
  · rw [S.par_of_inV ha, S.par_of_inV (h.mpr ha)]
  · rw [S.par_of_not_inV ha, S.par_of_not_inV (fun h' => ha (h.mp h'))]

abbrev cm (x y : G) : G := x⁻¹ * y * x * y⁻¹

theorem par_mul_self_mul [CharP K 2] {x y : G} (hx : x ∈ S.X) (hy : y ∈ S.X) :
    S.par (x * y * (x * y)) = S.par (x * x) + S.par (cm x y) + S.par (y * y) := by
  have e : x * y * (x * y) = x * x * cm x y * (y * y) := by simp only [cm]; group
  rw [e, S.par_mul ((S.inE_mul_self hx).mul (S.inE_comm hx hy)) (S.inE_mul_self hy),
    S.par_mul (S.inE_mul_self hx) (S.inE_comm hx hy)]

theorem par_cm_mul {x y z : G} (hx : x ∈ S.X) (hy : y ∈ S.X) (hz : z ∈ S.X) :
    S.par (cm x (y * z)) = S.par (cm x y) + S.par (cm x z) := by
  have e : cm x (y * z) = cm x y * (y * cm x z * y⁻¹) := by simp only [cm]; group
  rw [e, S.par_mul (S.inE_comm hx hy) ((S.inE_comm hx hz).conj hy), S.par_conj hy]

theorem par_mul_self_eq [CharP K 2] {x x' : G} (hx : x ∈ S.X) (hx' : x' ∈ S.X)
    (h : S.ψ x = S.ψ x') : S.par (x * x) = S.par (x' * x') := by
  have he : S.InE (x⁻¹ * x') :=
    ⟨mul_mem (inv_mem hx) hx', by rw [S.ψ_mul (inv_mem hx) hx', S.ψ_inv hx, h, neg_add_cancel]⟩
  have e : x' * x' = x * x * (x⁻¹ * (x⁻¹ * x') * x⁻¹⁻¹) * (x⁻¹ * x') := by group
  rw [e, S.par_mul ((S.inE_mul_self hx).mul (he.conj (inv_mem hx))) he,
    S.par_mul (S.inE_mul_self hx) (he.conj (inv_mem hx)), S.par_conj (inv_mem hx), add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

theorem par_mul_self_const [CharP K 2] {x x' : G} (hx : x ∈ S.X) (hx' : x' ∈ S.X)
    (h : S.ψ x ≠ 0) (h' : S.ψ x' ≠ 0) : S.par (x * x) = S.par (x' * x') := by
  obtain ⟨B, hB⟩ := exists_SL_mulVec_eq h h'
  have hy := S.lev_mem B x hx
  rw [← S.par_mul_self_eq hy hx' (by rw [S.ψ_lev hx, hB])]
  have e : S.lev B * x * (S.lev B)⁻¹ * (S.lev B * x * (S.lev B)⁻¹) =
      S.lev B * (x * x) * (S.lev B)⁻¹ := by group
  rw [e, S.par_lev]

theorem par_mul_self_of_ψ_eq_zero [CharP K 2] {x : G} (hx : x ∈ S.X) (h : S.ψ x = 0) :
    S.par (x * x) = 0 := by
  obtain ⟨v, rfl | rfl⟩ := S.exists_of_ψ_eq_zero hx h
  · exact S.par_of_inV ⟨v + v, S.ι_add v v⟩
  · have e : S.ι v * S.t * (S.ι v * S.t) = S.ι (v + v) := by
      rw [S.ι_add, mul_assoc, ← mul_assoc S.t, ← S.ι_comm_t, mul_assoc, S.t_mul_self, mul_one]
    rw [e]
    exact S.par_of_inV ⟨_, rfl⟩

theorem par_mul_self [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K) {x : G} (hx : x ∈ S.X) :
    S.par (x * x) = 0 := by
  by_contra hne
  have hψ : S.ψ x ≠ 0 := fun h => hne (S.par_mul_self_of_ψ_eq_zero hx h)
  have hone : ∀ y ∈ S.X, S.ψ y ≠ 0 → S.par (y * y) = 1 := by
    intro y hy hψy
    rw [← S.par_mul_self_const hx hy hψ hψy]
    rcases (show ∀ p : ZMod 2, p = 0 ∨ p = 1 by decide) (S.par (x * x)) with h | h
    · exact absurd h hne
    · exact h
  obtain ⟨μ, hμ0, hμ1⟩ : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1 := by
    obtain ⟨u, hu⟩ := exists_unit_cube_ne_one hK
    exact ⟨u, u.ne_zero, fun h => hu (by rw [h, one_pow])⟩
  have hμ1' : 1 + μ ≠ 0 := fun h => hμ1 (by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h - h2)
  have hne0 : ∀ v : Fin 2 → K, v 0 ≠ 0 → v ≠ 0 := fun v hv h => hv (by rw [h]; rfl)
  have hne1 : ∀ v : Fin 2 → K, v 1 ≠ 0 → v ≠ 0 := fun v hv h => hv (by rw [h]; rfl)
  obtain ⟨x₁, hx₁, hψ₁⟩ := S.ψ_surj ![1, 0]
  obtain ⟨x₂, hx₂, hψ₂⟩ := S.ψ_surj ![0, 1]
  obtain ⟨x₃, hx₃, hψ₃⟩ := S.ψ_surj ![μ, 0]
  have key : ∀ y z : G, y ∈ S.X → z ∈ S.X → S.ψ y ≠ 0 → S.ψ z ≠ 0 → S.ψ (y * z) ≠ 0 →
      S.par (cm y z) = 1 := by
    intro y z hy hz h1 h2 h3
    have h := S.par_mul_self_mul hy hz
    rw [hone _ (mul_mem hy hz) h3, hone y hy h1, hone z hz h2] at h
    exact (show ∀ p : ZMod 2, (1 : ZMod 2) = 1 + p + 1 → p = 1 by decide) _ h
  have h12 := key x₁ x₂ hx₁ hx₂ (by rw [hψ₁]; exact hne0 _ one_ne_zero)
    (by rw [hψ₂]; exact hne1 _ one_ne_zero)
    (by rw [S.ψ_mul hx₁ hx₂, hψ₁, hψ₂]; exact hne0 _ (by simp))
  have h13 := key x₁ x₃ hx₁ hx₃ (by rw [hψ₁]; exact hne0 _ one_ne_zero)
    (by rw [hψ₃]; exact hne0 _ hμ0)
    (by rw [S.ψ_mul hx₁ hx₃, hψ₁, hψ₃]; exact hne0 _ (by simpa using hμ1'))
  have h123 := key x₁ (x₂ * x₃) hx₁ (mul_mem hx₂ hx₃) (by rw [hψ₁]; exact hne0 _ one_ne_zero)
    (by rw [S.ψ_mul hx₂ hx₃, hψ₂, hψ₃]; exact hne1 _ (by simp))
    (by rw [S.ψ_mul hx₁ (mul_mem hx₂ hx₃), S.ψ_mul hx₂ hx₃, hψ₁, hψ₂, hψ₃]
        exact hne1 _ (by simp))
  rw [S.par_cm_mul hx₁ hx₂ hx₃, h12, h13] at h123
  exact absurd h123 (by decide)

theorem inV_comm [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K) {x y : G} (hx : x ∈ S.X)
    (hy : y ∈ S.X) : S.InV (x * y * x⁻¹ * y⁻¹) := by
  apply S.inV_of_par
  have h := S.par_mul_self_mul (inv_mem hx) hy
  rw [S.par_mul_self hK (mul_mem (inv_mem hx) hy), S.par_mul_self hK (inv_mem hx),
    S.par_mul_self hK hy, zero_add, add_zero] at h
  have e : x * y * x⁻¹ * y⁻¹ = cm x⁻¹ y := by simp only [cm, inv_inv]
  rw [e, ← h]

abbrev kp (l : Kˣ) (z : G) : G := S.tor l * z * (S.tor l)⁻¹ * z⁻¹

theorem kp_mem {z : G} (hz : z ∈ S.X) (l : Kˣ) : S.kp l z ∈ S.X :=
  mul_mem (S.tor_mem l z hz) (inv_mem hz)

theorem ψ_kp {z : G} (hz : z ∈ S.X) (l : Kˣ) : S.ψ (S.kp l z) = ((l : K) ^ 3 - 1) • S.ψ z := by
  rw [S.ψ_mul (S.tor_mem l z hz) (inv_mem hz), S.ψ_tor hz, S.ψ_inv hz, sub_smul, one_smul,
    sub_eq_add_neg]

theorem kp_mul [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K) {z z' : G} (hz : z ∈ S.X)
    (hz' : z' ∈ S.X) (l : Kˣ) : ∃ w, S.kp l z * S.kp l z' = S.kp l (z * z') * S.ι w := by
  obtain ⟨w, hw⟩ := S.inV_comm hK hz (inv_mem (S.kp_mem hz' l))
  refine ⟨w, ?_⟩
  rw [hw]
  simp only [kp]
  group

theorem kp_inv [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K) {z : G} (hz : z ∈ S.X) (l : Kˣ) :
    ∃ w, (S.kp l z)⁻¹ = S.kp l z⁻¹ * S.ι w := by
  obtain ⟨w, hw⟩ := S.kp_mul hK (inv_mem hz) hz l
  rw [inv_mul_cancel] at hw
  have h1 : S.kp l 1 = 1 := by simp only [kp]; group
  rw [h1, one_mul] at hw
  refine ⟨-w, ?_⟩
  rw [← S.ι_comm (-w) _ (S.kp_mem (inv_mem hz) l), S.ι_neg, ← hw,
    _root_.mul_inv_rev (S.kp l z⁻¹) (S.kp l z), inv_mul_cancel_right]

@[expose] def Wsub [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K) (l : Kˣ) : Subgroup G where
  carrier := {x | x ∈ S.X ∧ ∃ z ∈ S.X, ∃ v, x = S.kp l z * S.ι v}
  one_mem' := ⟨one_mem _, 1, one_mem _, 0, by simp only [kp, S.ι_zero]; group⟩
  mul_mem' := by
    rintro a b ⟨ha, z, hz, v, rfl⟩ ⟨hb, z', hz', v', rfl⟩
    refine ⟨mul_mem ha hb, z * z', mul_mem hz hz', ?_⟩
    obtain ⟨w, hw⟩ := S.kp_mul hK hz hz' l
    refine ⟨w + (v + v'), ?_⟩
    have e1 : S.ι v * (S.kp l z' * S.ι v') = S.kp l z' * (S.ι v * S.ι v') := by
      rw [← mul_assoc, S.ι_comm v _ (S.kp_mem hz' l), mul_assoc]
    rw [S.ι_add, S.ι_add, mul_assoc, e1, ← mul_assoc, hw, mul_assoc]
  inv_mem' := by
    rintro a ⟨ha, z, hz, v, rfl⟩
    refine ⟨inv_mem ha, z⁻¹, inv_mem hz, ?_⟩
    obtain ⟨w, hw⟩ := S.kp_inv hK hz l
    refine ⟨w + -v, ?_⟩
    rw [_root_.mul_inv_rev, hw, ← S.ι_neg,
      S.ι_comm (-v) _ (mul_mem (S.kp_mem (inv_mem hz) l) (S.ι_mem w)), mul_assoc, ← S.ι_add]

theorem kp_one (l : Kˣ) : S.kp l 1 = 1 := by simp only [kp]; group

theorem kp_conj {g : G} (l : Kˣ) (hg : g * S.tor l = S.tor l * g) (z : G) :
    g * S.kp l z * g⁻¹ = S.kp l (g * z * g⁻¹) := by
  have h : g * S.tor l * g⁻¹ = S.tor l := by rw [hg, mul_inv_cancel_right]
  calc g * S.kp l z * g⁻¹ = (g * S.tor l * g⁻¹) * (g * z * g⁻¹) * (g * S.tor l * g⁻¹)⁻¹ *
      (g * z * g⁻¹)⁻¹ := by simp only [kp]; group
    _ = S.kp l (g * z * g⁻¹) := by rw [h]

theorem kp_ι (l : Kˣ) (v : Fin 2 → K) : S.kp l (S.ι v) = S.ι (((l : K) ^ 3 - 1) • v) := by
  rw [kp, S.tor_ι, ← S.ι_neg, ← S.ι_add, sub_smul, one_smul, sub_eq_add_neg]

theorem kp_ι_t (l : Kˣ) (v : Fin 2 → K) :
    S.kp l (S.ι v * S.t) = S.ι (((l : K) ^ 3 - 1) • v) := by
  have h : S.tor l * S.t * (S.tor l)⁻¹ = S.t := by rw [S.tor_t, mul_inv_cancel_right]
  calc S.kp l (S.ι v * S.t) = (S.tor l * S.ι v * (S.tor l)⁻¹) * (S.tor l * S.t * (S.tor l)⁻¹) *
      S.t⁻¹ * (S.ι v)⁻¹ := by simp only [kp]; group
    _ = S.kp l (S.ι v) := by rw [h, mul_inv_cancel_right]
    _ = _ := S.kp_ι l v

variable [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K) {l : Kˣ}

include hK in
theorem Wsub_le : S.Wsub hK l ≤ S.X := fun _ hx => hx.1

include hK in
theorem kp_mem_Wsub {z : G} (hz : z ∈ S.X) : S.kp l z ∈ S.Wsub hK l :=
  ⟨S.kp_mem hz l, z, hz, 0, by rw [S.ι_zero, mul_one]⟩

include hK in
theorem ι_mem_Wsub (v : Fin 2 → K) : S.ι v ∈ S.Wsub hK l :=
  ⟨S.ι_mem v, 1, one_mem _, v, by rw [S.kp_one, one_mul]⟩

include hK in
theorem exists_ι_of_mem_Wsub (hl : (l : K) ^ 3 ≠ 1) {x : G} (hx : x ∈ S.Wsub hK l)
    (h : S.ψ x = 0) : ∃ v, S.ι v = x := by
  obtain ⟨-, z, hz, v, rfl⟩ := hx
  rw [S.ψ_mul (S.kp_mem hz l) (S.ι_mem v), S.ψ_ι, add_zero, S.ψ_kp hz] at h
  have hz0 : S.ψ z = 0 := (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hl)
  obtain ⟨u, rfl | rfl⟩ := S.exists_of_ψ_eq_zero hz hz0
  · exact ⟨_, by rw [S.kp_ι, ← S.ι_add]⟩
  · exact ⟨_, by rw [S.kp_ι_t, ← S.ι_add]⟩

include hK in
theorem exists_mem_Wsub_ψ (hl : (l : K) ^ 3 ≠ 1) (ξ : Fin 2 → K) :
    ∃ x ∈ S.Wsub hK l, S.ψ x = ξ := by
  obtain ⟨z, hz, hψz⟩ := S.ψ_surj (((l : K) ^ 3 - 1)⁻¹ • ξ)
  refine ⟨_, S.kp_mem_Wsub hK hz, ?_⟩
  rw [S.ψ_kp hz, hψz, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hl), one_smul]

include hK in
theorem t_not_mem_Wsub (hl : (l : K) ^ 3 ≠ 1) : S.t ∉ S.Wsub hK l := fun h => by
  obtain ⟨v, hv⟩ := S.exists_ι_of_mem_Wsub hK hl h S.ψ_t
  exact S.t_ne_ι v hv.symm

include hK in
theorem mem_Wsub_or (hl : (l : K) ^ 3 ≠ 1) {x : G} (hx : x ∈ S.X) :
    x ∈ S.Wsub hK l ∨ x * S.t ∈ S.Wsub hK l := by
  obtain ⟨a, ha, hψa⟩ := S.exists_mem_Wsub_ψ hK hl (S.ψ x)
  have he : S.ψ (a⁻¹ * x) = 0 := by
    rw [S.ψ_mul (inv_mem ha.1) hx, S.ψ_inv ha.1, hψa, neg_add_cancel]
  obtain ⟨u, hu | hu⟩ := S.exists_of_ψ_eq_zero (mul_mem (inv_mem ha.1) hx) he
  · left
    rw [show x = a * (a⁻¹ * x) by group, hu]
    exact mul_mem ha (S.ι_mem_Wsub hK u)
  · right
    rw [show x = a * (a⁻¹ * x) by group, hu, mul_assoc, mul_assoc, S.t_mul_self, mul_one]
    exact mul_mem ha (S.ι_mem_Wsub hK u)

include hK in
theorem t_conj_mem_Wsub {x : G} (hx : x ∈ S.Wsub hK l) : S.t * x * S.t⁻¹ ∈ S.Wsub hK l := by
  have h : S.t * x * S.t⁻¹ = S.ι (S.ψ x) * x := by
    rw [S.ι_ψ hx.1, S.t_inv]; group
  rw [h]
  exact mul_mem (S.ι_mem_Wsub hK _) hx

@[expose] noncomputable def toWSetting (hl : (l : K) ^ 3 ≠ 1) : WSetting G K where
  W := S.Wsub hK l
  ι := S.ι
  ψ := S.ψ
  lev := S.lev
  tor := S.tor
  ι_add := S.ι_add
  ι_injective := S.ι_injective
  ι_mem := S.ι_mem_Wsub hK
  ι_comm v a ha := S.ι_comm v a ha.1
  comm_mem a ha b hb := by
    obtain ⟨v, hv⟩ := S.inV_comm hK ha.1 hb.1
    exact ⟨v, hv.symm⟩
  ψ_mul a ha b hb := S.ψ_mul ha.1 hb.1
  ψ_surj := S.exists_mem_Wsub_ψ hK hl
  ψ_eq_zero a ha h := S.exists_ι_of_mem_Wsub hK hl ha h
  ψ_ι := S.ψ_ι
  lev_mem B a ha := by
    obtain ⟨haX, z, hz, v, rfl⟩ := ha
    refine ⟨S.lev_mem B _ haX, _, S.lev_mem B z hz, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ v, ?_⟩
    rw [← S.lev_ι, ← S.kp_conj l (S.tor_lev l B).symm]
    group
  lev_ψ B a ha := S.ψ_lev ha.1 B
  lev_ι := S.lev_ι
  tor_mem l' a ha := by
    obtain ⟨haX, z, hz, v, rfl⟩ := ha
    have hc : S.tor l' * S.tor l = S.tor l * S.tor l' := by
      rw [← map_mul, ← map_mul, mul_comm]
    refine ⟨S.tor_mem l' _ haX, _, S.tor_mem l' z hz, ((l' : K) ^ 3) • v, ?_⟩
    rw [← S.tor_ι, ← S.kp_conj l hc]
    group
  tor_ψ l' a ha := S.ψ_tor ha.1 l'
  tor_ι := S.tor_ι
  tor_lev := S.tor_lev

end XSetting

end CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal
