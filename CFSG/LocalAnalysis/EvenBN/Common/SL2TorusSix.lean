module

public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusTwo
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusThree
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Matrix Subgroup CFSG.SL2MinimalFaithful
open scoped MatrixGroups

variable {k : Type*} [Field k] [CharP k 2]

theorem apply_apply_eq_of_mem_torusSL [Finite k] {n : ℕ} (hk : Nat.card k = (2 ^ n) ^ 2)
    {μ₀ : kˣ} (hμ₀ : orderOf μ₀ = 2 ^ n - 1) (φ : SL(2, k) ≃* SL(2, k))
    (hU : ∀ x ∈ upperSL k, φ x ∈ upperSL k) (hT : ∀ x ∈ torusSL k, φ x ∈ torusSL k)
    (hφμ₀ : φ (diagSL μ₀) = diagSL μ₀) {x : SL(2, k)} (hx : x ∈ torusSL k) : φ (φ x) = x := by
  have : Fintype k := Fintype.ofFinite k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hn : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := k)
    rw [hk] at this
    norm_num at this
  have hσex : ∀ μ : kˣ, ∃ ν : kˣ, diagSL ν = φ (diagSL μ) := fun μ =>
    hT _ (diagSL_mem_torusSL μ)
  choose σ hσ using hσex
  have hβex : ∀ c : k, ∃ c' : k, unipotent c' = φ (unipotent c) := fun c =>
    mem_upperSL_iff.1 (hU _ (unipotent_mem_upperSL c))
  choose β hβ using hβex
  have hβadd : ∀ a b, β (a + b) = β a + β b := by
    intro a b
    apply unipotent_injective
    rw [hβ, unipotent_add, map_mul, ← hβ, ← hβ, unipotent_add]
  have hβ0 : β 0 = 0 := unipotent_injective (by rw [hβ, unipotent_zero, map_one])
  have hβ1 : β 1 ≠ 0 := by
    intro h
    have e : φ (unipotent 1) = φ (unipotent 0) := by rw [← hβ, h, ← hβ, hβ0]
    exact one_ne_zero (unipotent_injective (φ.injective e))
  have hE : ∀ (μ : kˣ) (c : k), β ((μ : k) ^ 2 * c) = ((σ μ : kˣ) : k) ^ 2 * β c := by
    intro μ c
    apply unipotent_injective
    rw [hβ, ← diagSL_conj_unipotent, map_mul, map_mul, map_inv, ← hσ, ← hβ,
      diagSL_conj_unipotent]
  set τ : k → k := fun c => β c * (β 1)⁻¹ with hτ
  have hτsq : ∀ μ : kˣ, τ ((μ : k) ^ 2) = ((σ μ : kˣ) : k) ^ 2 := by
    intro μ
    have e := hE μ 1
    rw [mul_one] at e
    simp only [hτ, e, mul_assoc, mul_inv_cancel₀ hβ1, mul_one]
  have hτadd : ∀ a b, τ (a + b) = τ a + τ b := fun a b => by simp only [hτ, hβadd, add_mul]
  have hτ0 : τ 0 = 0 := by simp only [hτ, hβ0, zero_mul]
  have hτ1 : τ 1 = 1 := mul_inv_cancel₀ hβ1
  have hτmul : ∀ a b, τ (a * b) = τ a * τ b := by
    intro a b
    by_cases ha : a = 0
    · rw [ha, zero_mul, hτ0, zero_mul]
    · obtain ⟨ρ, hρ⟩ := exists_units_sq_eq (Units.mk0 a ha)
      have hρa : (ρ : k) ^ 2 = a := by rw [← Units.val_pow_eq_pow_val, hρ, Units.val_mk0]
      rw [← hρa, hτsq]
      simp only [hτ, hE]
      ring
  have hτpow : ∀ (a : k) (i : ℕ), τ (a ^ i) = τ a ^ i := by
    intro a i
    induction i with
    | zero => simp only [pow_zero, hτ1]
    | succ i ih => rw [pow_succ, hτmul, ih, pow_succ]
  have hσμ₀ : σ μ₀ = μ₀ := diagSL_injective ((hσ μ₀).trans hφμ₀)
  have hτμ₀ : τ ((μ₀ : k) ^ 2) = (μ₀ : k) ^ 2 := by rw [hτsq, hσμ₀]
  have hr1 : 2 ^ n - 1 ≠ 0 := by
    have : 2 ≤ 2 ^ n := Nat.le_self_pow hn 2
    omega
  have : NeZero (2 ^ n - 1) := ⟨hr1⟩
  have hprim : IsPrimitiveRoot ((μ₀ : k) ^ 2) (2 ^ n - 1) := by
    have hodd : Odd (2 ^ n - 1) := by
      have : 2 ≤ 2 ^ n := Nat.le_self_pow hn 2
      obtain ⟨j, hj⟩ : 2 ∣ 2 ^ n := dvd_pow_self 2 hn
      exact ⟨j - 1, by omega⟩
    have hcop : (orderOf (μ₀ : k)).Coprime 2 := by
      rw [orderOf_units, hμ₀]
      exact Nat.Coprime.symm ((Nat.coprime_two_left).2 hodd)
    have := IsPrimitiveRoot.orderOf ((μ₀ : k) ^ 2)
    rwa [hcop.orderOf_pow, orderOf_units, hμ₀] at this
  have hfix : ∀ x : k, x ^ 2 ^ n = x → τ x = x := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0, hτ0]
    · have hx1 : x ^ (2 ^ n - 1) = 1 := by
        have : x ^ (2 ^ n - 1) * x = 1 * x := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow), hx, one_mul]
        exact mul_right_cancel₀ hx0 this
      obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hx1
      rw [hτpow, hτμ₀]
  have hqk : Fintype.card k = 2 ^ n * 2 ^ n := by rw [← Nat.card_eq_fintype_card, hk, sq]
  have hτinv : ∀ α : k, τ (τ α) = α := by
    intro α
    set a := α + α ^ 2 ^ n with ha
    set b := α * α ^ 2 ^ n with hb
    have hαq : (α ^ 2 ^ n) ^ 2 ^ n = α := by
      rw [← pow_mul, ← hqk, FiniteField.pow_card]
    have hfa : τ a = a := hfix a (by rw [ha, add_pow_char_pow, hαq, add_comm])
    have hfb : τ b = b := hfix b (by rw [hb, mul_pow, hαq, mul_comm])
    have hroot : α ^ 2 + a * α + b = 0 := by
      rw [ha, hb]
      linear_combination (α ^ 2 + α ^ 2 ^ n * α) * h2
    have hτroot : τ α ^ 2 + a * τ α + b = 0 := by
      have := congrArg τ hroot
      rwa [hτadd, hτadd, hτmul, hτpow, hfa, hfb, hτ0] at this
    have hfac : (τ α + α) * (τ α + (α + a)) = 0 := by
      linear_combination hτroot + hroot + (α * τ α - b) * h2
    rcases mul_eq_zero.1 hfac with h | h
    · rw [CharTwo.add_eq_zero.1 h, CharTwo.add_eq_zero.1 h]
    · rw [CharTwo.add_eq_zero.1 h, hτadd, CharTwo.add_eq_zero.1 h, hfa]
      linear_combination a * h2
  have hσσ : ∀ μ : kˣ, σ (σ μ) = μ := by
    intro μ
    apply Units.ext
    apply CharTwo.sq_injective
    show ((σ (σ μ) : kˣ) : k) ^ 2 = (μ : k) ^ 2
    rw [← hτsq (σ μ), ← hτsq μ, hτinv]
  obtain ⟨μ, rfl⟩ := hx
  rw [diagSLHom_apply, ← hσ, ← hσ, hσσ]

theorem apply_eq_of_mem_torusSL_of_odd [Finite k] {n : ℕ} (hk : Nat.card k = (2 ^ n) ^ 2)
    {μ₀ : kˣ} (hμ₀ : orderOf μ₀ = 2 ^ n - 1) (φ : MulAut SL(2, k))
    (hU : ∀ x ∈ upperSL k, φ x ∈ upperSL k) (hT : ∀ x ∈ torusSL k, φ x ∈ torusSL k)
    (hφμ₀ : φ (diagSL μ₀) = diagSL μ₀) {m : ℕ} (hm : Odd m) (hφm : φ ^ m = 1) {x : SL(2, k)}
    (hx : x ∈ torusSL k) : φ x = x := by
  have h2 : (φ ^ 2) x = x := by
    rw [sq, MulAut.mul_apply]
    exact apply_apply_eq_of_mem_torusSL hk hμ₀ φ hU hT hφμ₀ hx
  have hpow : ∀ j : ℕ, ((φ ^ 2) ^ j) x = x := by
    intro j
    induction j with
    | zero => rw [pow_zero, MulAut.one_apply]
    | succ j ih => rw [pow_succ, MulAut.mul_apply, h2, ih]
  obtain ⟨j, rfl⟩ := hm
  have e : (φ ^ (2 * j + 1)) x = x := by rw [hφm, MulAut.one_apply]
  rwa [pow_succ', pow_mul, MulAut.mul_apply, hpow] at e

theorem coe_normalizerMonoidHom_apply {G : Type*} [Group G] {X : Subgroup G}
    (g : normalizer (X : Set G)) (y : X) :
    ((X.normalizerMonoidHom g y : X) : G) = (g : G) * y * (g : G)⁻¹ :=
  rfl

theorem commute_of_odd_of_mem_normalizer [Finite k] {n : ℕ} (hk : Nat.card k = (2 ^ n) ^ 2)
    {G : Type*} [Group G] {X W : Subgroup G} (ψ : X ≃* SL(2, k)) {d : G} (hdX : d ∈ X)
    (hd1 : d ≠ 1) (hd : orderOf d = 2 ^ n - 1) (hWX : W ≤ X) (hW : Nat.card W = Nat.card k)
    (hdW : d ∈ normalizer (W : Set G)) {g : G} (hg : Odd (orderOf g))
    (hgX : g ∈ normalizer (X : Set G)) (hgW : g ∈ normalizer (W : Set G)) (hgd : g * d = d * g)
    {c : G} (hcX : c ∈ X) (hcd : c * d = d * c) : g * c = c * g := by
  set d' : X := ⟨d, hdX⟩ with hd'
  set W' : Subgroup X := W.subgroupOf X with hW'
  have hW'card : Nat.card W' = Nat.card k := by
    rw [hW', Nat.card_congr (subgroupOfEquivOfLe hWX).toEquiv, hW]
  have hd'W' : d' ∈ normalizer (W' : Set X) := by
    rw [mem_normalizer_iff]
    intro w
    exact mem_normalizer_iff.1 hdW w
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hord : orderOf d' = 2 ^ n - 1 := by rw [← Subgroup.orderOf_coe]; exact hd
  have hq : Nat.card k - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ n = t + 1 := ⟨2 ^ n - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
    rw [hk, ht, Nat.add_sub_cancel, show (t + 1) ^ 2 = t * (t + 1 + 1) + 1 by ring,
      Nat.add_sub_cancel]
  have hd'q : d' ^ (Nat.card k - 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (hord ▸ hq ▸ dvd_mul_right _ _)
  obtain ⟨ψ₁, μ, hμ1, hψ₁d⟩ := exists_mulEquiv_eq_diagSL ψ hd'1 hd'q
  have hordμ : orderOf μ = 2 ^ n - 1 := by
    rw [← orderOf_injective diagSLHom diagSL_injective μ, diagSLHom_apply, ← hψ₁d,
      MulEquiv.orderOf_eq, hord]
  obtain ⟨ψ₂, ν, hν1, hψ₂d, hordν, hψ₂W⟩ : ∃ (ψ₂ : X ≃* SL(2, k)) (ν : kˣ), ν ≠ 1 ∧
      ψ₂ d' = diagSL ν ∧ orderOf ν = 2 ^ n - 1 ∧ W'.map ψ₂.toMonoidHom = upperSL k := by
    have hcard : Nat.card (W'.map ψ₁.toMonoidHom) = Nat.card k := by
      rw [card_map_of_injective ψ₁.injective, hW'card]
    have hnorm : diagSL μ ∈ normalizer ((W'.map ψ₁.toMonoidHom : Subgroup SL(2, k)) :
        Set SL(2, k)) := by
      rw [← map_equiv_normalizer_eq, ← hψ₁d]
      exact ⟨d', hd'W', rfl⟩
    rcases eq_upperSL_or_eq_lowerSL hcard hμ1 hnorm with h | h
    · exact ⟨ψ₁, μ, hμ1, hψ₁d, hordμ, h⟩
    · refine ⟨ψ₁.trans (MulAut.conj (weylSL k)), μ⁻¹, inv_ne_one.2 hμ1, ?_,
        by rw [orderOf_inv, hordμ], ?_⟩
      · rw [MulEquiv.trans_apply, hψ₁d, MulAut.conj_apply, weylSL_conj_diagSL]
      · rw [← map_conj_weylSL_lowerSL, ← h, Subgroup.map_map]
        rfl
  set gN : normalizer (X : Set G) := ⟨g, hgX⟩ with hgN
  set φ : MulAut SL(2, k) := MulAut.congr ψ₂ (X.normalizerMonoidHom gN) with hφ
  have hφX : ∀ y : X, φ (ψ₂ y) = ψ₂ (X.normalizerMonoidHom gN y) := fun y => by
    simp [hφ, MulAut.congr_apply]
  have hφm : φ ^ orderOf g = 1 := by
    have : gN ^ orderOf g = 1 := Subtype.ext (by simp [hgN, pow_orderOf_eq_one])
    rw [hφ, ← map_pow, ← map_pow, this, map_one, map_one]
  have hφd : φ (diagSL ν) = diagSL ν := by
    have : X.normalizerMonoidHom gN d' = d' := Subtype.ext (by
      rw [coe_normalizerMonoidHom_apply]
      show g * d * g⁻¹ = d
      rw [hgd, mul_inv_cancel_right])
    rw [← hψ₂d, hφX, this]
  have hU : ∀ x ∈ upperSL k, φ x ∈ upperSL k := by
    rw [← hψ₂W]
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨X.normalizerMonoidHom gN w, (mem_normalizer_iff.1 hgW w).1 hw, (hφX w).symm⟩
  have hTX : (centralizer ({d'} : Set X)).map ψ₂.toMonoidHom = torusSL k := by
    rw [← centralizer_zpowers, map_centralizer_zpowers_eq_torusSL ψ₂ hν1 hψ₂d]
  have hgd'' : Commute g d := hgd
  have hT : ∀ x ∈ torusSL k, φ x ∈ torusSL k := by
    rw [← hTX]
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨X.normalizerMonoidHom gN y, ?_, (hφX y).symm⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy ⊢
    have hy' : Commute (y : G) d := congrArg Subtype.val hy
    exact Subtype.ext ((hgd''.mul_left hy').mul_left hgd''.inv_left)
  have hc' : (⟨c, hcX⟩ : X) ∈ centralizer ({d'} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext hcd
  have hψc : ψ₂ ⟨c, hcX⟩ ∈ torusSL k := hTX ▸ ⟨_, hc', rfl⟩
  have key := apply_eq_of_mem_torusSL_of_odd hk hordν φ hU hT hφd hg hφm hψc
  rw [hφX] at key
  have := congrArg Subtype.val (ψ₂.injective key)
  rw [coe_normalizerMonoidHom_apply] at this
  exact mul_inv_eq_iff_eq_mul.1 this

end CFSG.LocalAnalysis.EvenBN.Common
