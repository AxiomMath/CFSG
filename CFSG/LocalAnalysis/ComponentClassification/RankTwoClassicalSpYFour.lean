module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpYAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSym
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44Defs

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section FourField

variable {K : Type} [Field K]

theorem eq_zero_or_eq_one_or_of_card_four [Finite K] (hK : Nat.card K = 4) (a : K) :
    a = 0 ∨ a = 1 ∨ a * a + a + 1 = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h4 : a ^ 4 = a := by
    have := FiniteField.pow_card a
    rwa [← Nat.card_eq_fintype_card, hK] at this
  have h : a * (a - 1) * (a * a + a + 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr h)

theorem eq_of_card_four_of_fix [Finite K] (hK : Nat.card K = 4) {t : K} (ht : t * t + t + 1 = 0)
    {φ : K ≃+* K} (hφ : φ t = t) (a : K) : φ a = a := by
  rcases eq_zero_or_eq_one_or_of_card_four hK a with rfl | rfl | ha
  · exact map_zero φ
  · exact map_one φ
  · have h : (a - t) * (a + t + 1) = 0 := by linear_combination ha - ht
    rcases mul_eq_zero.mp h with h | h
    · rw [sub_eq_zero.mp h, hφ]
    · have hat : a = -(t + 1) := by linear_combination h
      rw [hat, map_neg, map_add, map_one, hφ]

theorem mul_smul_add_smul_one {B : Matrix (Fin 2) (Fin 2) K} {t : K} (hB : B * B = t • B + 1)
    (p q : K) :
    B * (p • B + q • (1 : Matrix (Fin 2) (Fin 2) K)) = (t * p + q) • B + p • 1 := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hB, Matrix.mul_one]
  module

variable [CharP K 2]

theorem pow_three_eq_one_of_trace (X : SL(2, K)) (ht : X 0 0 + X 1 1 = 1) : X ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hB := mul_self_eq_add X
  rw [ht] at hB
  have hB' : (X : Matrix (Fin 2) (Fin 2) K) * X =
      (1 : K) • (X : Matrix (Fin 2) (Fin 2) K) + (1 : K) • 1 := by
    rw [hB, one_smul K (1 : Matrix (Fin 2) (Fin 2) K)]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_succ', pow_two,
    hB', mul_smul_add_smul_one hB, show (1 : K) * 1 + 1 = 0 by linear_combination h2, zero_smul,
    zero_add, one_smul]

theorem pow_five_eq_one_of_trace (X : SL(2, K))
    (ht : (X 0 0 + X 1 1) * (X 0 0 + X 1 1) + (X 0 0 + X 1 1) + 1 = 0) : X ^ 5 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set t := X 0 0 + X 1 1 with htdef
  have hB : (X : Matrix (Fin 2) (Fin 2) K) * X = t • (X : Matrix (Fin 2) (Fin 2) K) + 1 :=
    mul_self_eq_add X
  have hB' : (X : Matrix (Fin 2) (Fin 2) K) * X =
      t • (X : Matrix (Fin 2) (Fin 2) K) + (1 : K) • 1 := by
    rw [hB, one_smul K (1 : Matrix (Fin 2) (Fin 2) K)]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    show (5 : ℕ) = 1 + 1 + 1 + 1 + 1 from rfl, pow_succ', pow_succ', pow_succ', pow_succ', pow_one,
    hB', mul_smul_add_smul_one hB, mul_smul_add_smul_one hB, mul_smul_add_smul_one hB,
    show t * (t * (t * t + 1) + t) + (t * t + 1) = 0 by
      linear_combination (t * t - t + 3) * ht + (-t - 1) * h2,
    show t * (t * t + 1) + t = 1 by linear_combination (t - 1) * ht + t * h2, zero_smul, zero_add,
    one_smul]

theorem pow_eq_one_of_card_four [Finite K] (hK : Nat.card K = 4) (b : SL(2, K)) :
    b * b = 1 ∨ b ^ 3 = 1 ∨ b ^ 5 = 1 := by
  rcases eq_zero_or_eq_one_or_of_card_four hK (b 0 0 + b 1 1) with h | h | h
  · left
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, mul_self_eq_add, h, zero_smul, zero_add,
      Matrix.SpecialLinearGroup.coe_one]
  · exact Or.inr (Or.inl (pow_three_eq_one_of_trace b h))
  · exact Or.inr (Or.inr (pow_five_eq_one_of_trace b h))

theorem trace_mul_self_add_of_orderOf_five [Finite K] (hK : Nat.card K = 4) {X : SL(2, K)}
    (hX : orderOf X = 5) :
    (X 0 0 + X 1 1) * (X 0 0 + X 1 1) + (X 0 0 + X 1 1) + 1 = 0 := by
  rcases eq_zero_or_eq_one_or_of_card_four hK (X 0 0 + X 1 1) with h | h | h
  · exfalso
    have hXX : X * X = 1 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, mul_self_eq_add, h, zero_smul, zero_add,
        Matrix.SpecialLinearGroup.coe_one])
    have h2 : orderOf X ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hXX)
    rw [hX] at h2
    norm_num at h2
  · exfalso
    have h3 := orderOf_dvd_of_pow_eq_one (pow_three_eq_one_of_trace X h)
    rw [hX] at h3
    norm_num at h3
  · exact h

theorem eq_one_of_commute_of_pow_eq_one [Finite K] (hK : Nat.card K = 4) {a X : SL(2, K)}
    (hX : orderOf X = 5) (hc : a * X = X * a) {k : ℕ} (hk : a ^ 3 ^ k = 1) : a = 1 := by
  have hX5 : X ^ 5 = 1 := hX ▸ pow_orderOf_eq_one X
  have hX1 : X ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hX
    norm_num at hX
  have hcop : ∀ n, Nat.Coprime n (3 ^ k) → a ^ n = 1 → a = 1 := fun n hn han =>
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hn (orderOf_dvd_of_pow_eq_one han)
      (orderOf_dvd_of_pow_eq_one hk))
  have hcomm : Commute a X := hc
  rcases pow_eq_one_of_card_four hK a with h | h | h
  · exact hcop 2 (Nat.Coprime.pow_right _ (by norm_num)) (by rw [sq]; exact h)
  · rcases pow_eq_one_of_card_four hK (a * X) with h' | h' | h'
    · exfalso
      apply hX1
      have e : (a * X) ^ 6 = 1 := by
        rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, sq, h', one_pow]
      rw [hcomm.mul_pow, show (6 : ℕ) = 3 * 2 from rfl, pow_mul a, h, one_pow, one_mul] at e
      calc X = X ^ (3 * 2) * (X ^ 5)⁻¹ := by group
        _ = 1 := by rw [e, hX5, inv_one, mul_one]
    · exfalso
      apply hX1
      rw [hcomm.mul_pow, h, one_mul] at h'
      calc X = (X ^ 3) ^ 2 * (X ^ 5)⁻¹ := by group
        _ = 1 := by rw [h', hX5, one_pow, inv_one, mul_one]
    · rw [hcomm.mul_pow, hX5, mul_one] at h'
      exact hcop 5 (Nat.Coprime.pow_right _ (by norm_num)) h'
  · exact hcop 5 (Nat.Coprime.pow_right _ (by norm_num)) h

end FourField

section Trace

open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)

variable {K : Type} [Field K]

theorem trace_mat_spW_one [CharP K 2] (X : SL(2, K)) :
    (mat (1 + 1) K (spW K 1 X)).trace = X 0 0 + X 1 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [spW, mat_longBlock, Matrix.trace]
  simp [Fintype.sum_sum_type, Fin.sum_univ_two, blockMat]
  linear_combination h2

theorem trace_eq_of_conj_fieldSp {n : ℕ} {g M N : StatedSp n K} {φ : K ≃+* K}
    (h : g * fieldSp n K φ M * g⁻¹ = N) : φ (mat n K M).trace = (mat n K N).trace := by
  have h1 : (mat n K (fieldSp n K φ M)).trace = φ (mat n K M).trace := by
    change ((mat n K M).map φ).trace = _
    rw [Matrix.trace, Matrix.trace, map_sum]
    rfl
  rw [← h1, ← h, map_mul, map_mul, Matrix.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one,
    Matrix.one_mul]

end Trace

section FourAut

open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (spInner spInner_eq_conj
  spInner_mul_fieldAut_proj spInner_injective)

variable {K : Type} [Field K] {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSp (1 + 1) K)} [Finite K] [CharP K 2]

theorem outerFree_spY_four (hK : Nat.card K = 4) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (h4 : ∃ s : Finset K, s.card = 4) {X : SL(2, K)}
    (hX : orderOf X = 5) {y : G} (hyA : y ∈ A) (hyθ : θ ⟨y, hyA⟩ = proj (1 + 1) K (spW K 1 X))
    (σ : MulAut ↥A) (hσ : σ * σ = 1) (hfix : ∀ x : ↥A, (x : G) ∈ zpowers y → σ x = x) :
    ∃ l ∈ spLeviL θ, ∀ z : ↥A, (z : G) ∈ spLeviL θ → ((σ z : ↥A) : G) = l * z * l⁻¹ := by
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hy : α (proj (1 + 1) K (spW K 1 X)) = proj (1 + 1) K (spW K 1 X) := by
    rw [← hyθ, hα, hfix ⟨y, hyA⟩ (mem_zpowers y)]
  obtain ⟨g, φ, hαeq⟩ := exists_eq_spInner_mul_fieldAut_of_four hK (inducedAut_sq hθ hσ hα)
  have hy' := hy
  rw [hαeq, spInner_mul_fieldAut_proj] at hy'
  have htr := trace_eq_of_conj_fieldSp (proj_sp_injective hy')
  rw [trace_mat_spW_one] at htr
  have hφ := eq_of_card_four_of_fix hK (trace_mul_self_add_of_orderOf_five hK hX) htr
  rw [fieldAut_sp_eq_one hφ, mul_one] at hαeq
  rw [hαeq, spInner_eq_conj, conj_proj_sp] at hy
  have hc : g * spW K 1 X = spW K 1 X * g := by
    have h := proj_sp_injective hy
    calc g * spW K 1 X = g * spW K 1 X * g⁻¹ * g := by group
      _ = spW K 1 X * g := by rw [h]
  have hXdet : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0 :=
    det_sub_one_ne_zero_of_mul_self_ne_one fun hXX => by
      have h2 : orderOf X ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hXX)
      rw [hX] at h2
      norm_num at h2
  obtain ⟨a, h, rfl, -⟩ := exists_spWL_of_commute hXdet hc
  refine exists_inner_levLift_of hker hθ (commutator_spBarL h4) σ hα
    (lb := proj (1 + 1) K (spL K 1 h)) ⟨h, rfl⟩ fun x hx => ?_
  rw [hαeq, spInner_eq_conj, MulAut.conj_apply, spWL_apply, map_mul]
  have hmem : proj (1 + 1) K (spL K 1 h) * x * (proj (1 + 1) K (spL K 1 h))⁻¹ ∈ spBarL K 1 :=
    mul_mem (mul_mem ⟨h, rfl⟩ hx) (inv_mem ⟨h, rfl⟩)
  calc proj (1 + 1) K (spW K 1 a) * proj (1 + 1) K (spL K 1 h) * x *
        (proj (1 + 1) K (spW K 1 a) * proj (1 + 1) K (spL K 1 h))⁻¹ =
      proj (1 + 1) K (spW K 1 a) * (proj (1 + 1) K (spL K 1 h) * x *
        (proj (1 + 1) K (spL K 1 h))⁻¹) * (proj (1 + 1) K (spW K 1 a))⁻¹ := by group
    _ = proj (1 + 1) K (spL K 1 h) * x * (proj (1 + 1) K (spL K 1 h))⁻¹ := by
      rw [spBarW_commute_spBarL (x := proj (1 + 1) K (spW K 1 a)) ⟨a, rfl⟩ hmem,
        mul_inv_cancel_right]

theorem noThree_spY_four (hK : Nat.card K = 4) (hA : commutator ↥A = ⊤)
    (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ) (h4 : ∃ s : Finset K, s.card = 4)
    {X : SL(2, K)} (hX : orderOf X = 5) {y : G} (hyA : y ∈ A)
    (hyθ : θ ⟨y, hyA⟩ = proj (1 + 1) K (spW K 1 X)) :
    NoThreeCentralizing A (zpowers y ⊔ spLeviL θ) := by
  rintro σ ⟨k, hk⟩ hfix
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hαn : ∀ n : ℕ, ∀ a, (α ^ n) (θ a) = θ ((σ ^ n) a) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hα, ih]
  have hαk : α ^ 3 ^ k = 1 := by
    ext p
    obtain ⟨a, rfl⟩ := hθ p
    rw [hαn, hk]
    rfl
  have hL := inducedAut_fix_of_levLift hθ (commutator_spBarL h4) le_sup_right hfix hα
  have hy : α (proj (1 + 1) K (spW K 1 X)) = proj (1 + 1) K (spW K 1 X) := by
    rw [← hyθ, hα, hfix ⟨y, hyA⟩ (mem_sup_left (mem_zpowers y))]
  have hE : α ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spSemilinearAutGroup 2 K := by
    obtain ⟨-, -, hnorm, hidx⟩ :=
      CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := K)
    have hpow := Subgroup.pow_index_mem
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spSemilinearAutGroup 2 K) α
    have hne := Subgroup.index_ne_zero_of_finite
      (H := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spSemilinearAutGroup 2 K)
    obtain ⟨j, hj⟩ : Even (3 ^ k + 1) := (Odd.pow (⟨1, rfl⟩ : Odd 3)).add_one
    rcases (show (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spSemilinearAutGroup 2
        K).index = 1 ∨ (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spSemilinearAutGroup
        2 K).index = 2 by omega) with h1 | h1
    · rw [h1, pow_one] at hpow
      exact hpow
    · rw [h1] at hpow
      have hαj : α = (α ^ 2) ^ j := by
        rw [← pow_mul, show 2 * j = 3 ^ k + 1 by omega, pow_succ, hαk, one_mul]
      rw [hαj]
      exact pow_mem hpow j
  obtain ⟨g, φ, hαeq⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exists_eq_spInner_mul_fieldAut hE
  have hy' := hy
  rw [hαeq, spInner_mul_fieldAut_proj] at hy'
  have htr := trace_eq_of_conj_fieldSp (proj_sp_injective hy')
  rw [trace_mat_spW_one] at htr
  have hφ := eq_of_card_four_of_fix hK (trace_mul_self_add_of_orderOf_five hK hX) htr
  rw [fieldAut_sp_eq_one hφ, mul_one] at hαeq
  obtain ⟨-, a, rfl⟩ := fix_spBarL le_rfl g 1 fun l hl => by
    rw [map_one, mul_one, ← hαeq]
    exact hL l hl
  rw [hαeq, spInner_eq_conj, conj_proj_sp] at hy
  have h3 := proj_sp_injective hy
  rw [← map_inv, ← map_mul, ← map_mul] at h3
  have h4' := longBlock_injective _ h3
  have hcomm : a * X = X * a := by
    calc a * X = a * X * a⁻¹ * a := by group
      _ = X * a := by rw [h4']
  rw [hαeq, ← map_pow] at hαk
  have h5 := spInner_injective (hαk.trans (map_one _).symm)
  rw [← map_pow] at h5
  have h6 : a ^ 3 ^ k = 1 := longBlock_injective _ (h5.trans (map_one _).symm)
  have h1 : α = 1 := by
    rw [hαeq, eq_one_of_commute_of_pow_eq_one hK hX hcomm h6, map_one, map_one]
  exact eq_one_of_theta_eq hker hA σ fun a => by rw [← hα, h1, MulAut.one_apply]

end FourAut

end CFSG.ComponentClassification.RankTwoClassical
