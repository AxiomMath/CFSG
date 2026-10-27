module

public import CFSG.CGT.Timmesfeld75.ListWCLinMain
public import CFSG.CGT.Timmesfeld75.ListWCLinSylow

public section

namespace CFSG.CGT.Timmesfeld75

open Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2] {m : ℕ}

theorem sl_wc_dichotomy {T : Subgroup SL(m, K)} (hT : IsWC T) {t₀ : SL(m, K)} (ht₀T : t₀ ∈ T)
    {c φ : Fin m → K} (hc : c ≠ 0) (hφ : φ ≠ 0) (hφc : φ ⬝ᵥ c = 0)
    (ht₀ : (t₀ : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec c φ) :
    (∀ x ∈ T, ∀ v : Fin m → K, ∃ μ : K, ((x : Matrix (Fin m) (Fin m) K) - 1) *ᵥ v = μ • c) ∨
    (∀ x ∈ T, ∀ w : Fin m → K, ∃ μ : K, w ᵥ* ((x : Matrix (Fin m) (Fin m) K) - 1) = μ • φ) := by
  by_contra hcon
  simp only [not_or, not_forall, not_exists, exists_prop] at hcon
  obtain ⟨⟨x₁, hx₁, v₀, hv₀⟩, ⟨x₂, hx₂, w₀, hw₀⟩⟩ := hcon
  have hinv : ∀ {x : SL(m, K)}, x ∈ T → x * x = 1 := fun hx => elemAbelian_mul_self hT.1 hx
  have hfix : ∀ {x : SL(m, K)}, x ∈ T →
      (x : Matrix (Fin m) (Fin m) K) *ᵥ c = c ∧ φ ᵥ* (x : Matrix (Fin m) (Fin m) K) = φ :=
    fun hx => fix_of_commute_tv hc hφ ht₀ (elemAbelian_mul_comm hT.1 hx ht₀T) (hinv hx)
  have hN : ∀ {x : SL(m, K)}, x ∈ T → x ≠ 1 → ∀ g : SL(m, K), g * x = x * g →
      ∀ y ∈ T, g * y * g⁻¹ ∈ T := fun hx hx1 g hg y hy =>
    (Subgroup.mem_normalizer_iff.1 (hT.centralizer_le_normalizer hx hx1
      (Subgroup.mem_centralizer_singleton_iff.2 hg)) y).1 hy
  have hNN : ∀ {x : SL(m, K)}, x ∈ T →
      ((x : Matrix (Fin m) (Fin m) K) - 1) * ((x : Matrix (Fin m) (Fin m) K) - 1) = 0 :=
    fun hx => mul_self_sub_one_eq_zero (by
      have := congrArg (fun y : SL(m, K) => (y : Matrix (Fin m) (Fin m) K)) (hinv hx)
      simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
        using this)
  have hcommx : ∀ {x g : SL(m, K)}, (g : Matrix (Fin m) (Fin m) K) *
      ((x : Matrix (Fin m) (Fin m) K) - 1) =
      ((x : Matrix (Fin m) (Fin m) K) - 1) * (g : Matrix (Fin m) (Fin m) K) → g * x = x * g := by
    intro x g h
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    have e1 : (x : Matrix (Fin m) (Fin m) K) = 1 + ((x : Matrix (Fin m) (Fin m) K) - 1) := by
      abel
    rw [e1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h]
  have hx₁1 : x₁ ≠ 1 := by
    rintro rfl
    apply hv₀ 0
    rw [Matrix.SpecialLinearGroup.coe_one, sub_self, zero_mulVec, zero_smul]
  obtain ⟨g₁, hg₁N, hg₁c⟩ := exists_commute_move (hNN hx₁) hc
    (by rw [sub_mulVec, one_mulVec, (hfix hx₁).1, sub_self]) hv₀
  have ht₁T : g₁ * t₀ * g₁⁻¹ ∈ T := hN hx₁ hx₁1 g₁ (hcommx hg₁N) t₀ ht₀T
  have ht₁ := coe_conj_of_coe g₁ ht₀
  set d₁ := (g₁ : Matrix (Fin m) (Fin m) K) *ᵥ c with hd₁
  set φ₁ := φ ᵥ* ((g₁⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) with hφ₁
  have hd₁0 : d₁ ≠ 0 := mulVec_ne_zero' g₁ hc
  have hφ₁0 : φ₁ ≠ 0 := vecMul_ne_zero' _ hφ
  have hφ₁d₁ : φ₁ ⬝ᵥ d₁ = 0 := by
    rw [hφ₁, hd₁, ← dotProduct_mulVec, inv_mulVec_mulVec', hφc]
  by_cases hφ₁φ : ∃ l : K, φ₁ = l • φ
  swap
  · push Not at hφ₁φ
    exact false_of_two_tv hT ht₀T ht₁T ht₀ ht₁ hc hφ hφc hd₁0 hφ₁0 hφ₁d₁ hg₁c hφ₁φ
  obtain ⟨l, hl⟩ := hφ₁φ
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hl
    exact hφ₁0 hl
  have ht₁' : ((g₁ * t₀ * g₁⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      1 + vecMulVec (l • d₁) φ := by
    rw [ht₁, hl, vecMulVec_smul, ← smul_vecMulVec]
  have he₁0 : l • d₁ ≠ 0 := smul_ne_zero hl0 hd₁0
  have he₁c : ∀ μ : K, l • d₁ ≠ μ • c := fun μ h => hg₁c (l⁻¹ * μ) (by
    rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hl0, one_smul])
  have hφe₁ : φ ⬝ᵥ (l • d₁) = 0 := by
    rw [hl, smul_dotProduct, smul_eq_mul] at hφ₁d₁
    rw [dotProduct_smul, smul_eq_mul]
    exact hφ₁d₁
  have hx₂1 : x₂ ≠ 1 := by
    rintro rfl
    apply hw₀ 0
    rw [Matrix.SpecialLinearGroup.coe_one, sub_self, vecMul_zero, zero_smul]
  obtain ⟨g₂, hg₂N, hg₂φ⟩ := exists_commute_move' (hNN hx₂) hφ
    (by rw [vecMul_sub, vecMul_one, (hfix hx₂).2, sub_self]) hw₀
  have hg₂x : g₂⁻¹ * x₂ = x₂ * g₂⁻¹ := by
    have h := hcommx hg₂N
    calc g₂⁻¹ * x₂ = g₂⁻¹ * (x₂ * g₂) * g₂⁻¹ := by group
      _ = g₂⁻¹ * (g₂ * x₂) * g₂⁻¹ := by rw [h]
      _ = x₂ * g₂⁻¹ := by group
  have ht₂T : g₂⁻¹ * t₀ * g₂⁻¹⁻¹ ∈ T := hN hx₂ hx₂1 g₂⁻¹ hg₂x t₀ ht₀T
  have ht₂ := coe_conj_of_coe g₂⁻¹ ht₀
  rw [inv_inv] at ht₂ ht₂T
  set d₂ := ((g₂⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) *ᵥ c with hd₂
  set φ₂ := φ ᵥ* (g₂ : Matrix (Fin m) (Fin m) K) with hφ₂
  have hd₂0 : d₂ ≠ 0 := mulVec_ne_zero' _ hc
  have hφ₂0 : φ₂ ≠ 0 := vecMul_ne_zero' _ hφ
  have hφ₂d₂ : φ₂ ⬝ᵥ d₂ = 0 := by
    rw [hφ₂, hd₂, ← dotProduct_mulVec, mulVec_inv_mulVec', hφc]
  by_cases hd₂c : ∃ k : K, d₂ = k • c
  swap
  · push Not at hd₂c
    exact false_of_two_tv hT ht₀T ht₂T ht₀ ht₂ hc hφ hφc hd₂0 hφ₂0 hφ₂d₂ hd₂c hg₂φ
  obtain ⟨k, hk⟩ := hd₂c
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hk
    exact hd₂0 hk
  have ht₂' : ((g₂⁻¹ * t₀ * g₂ : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      1 + vecMulVec c (k • φ₂) := by
    rw [ht₂, hk, smul_vecMulVec, ← vecMulVec_smul]
  have hψ0 : k • φ₂ ≠ 0 := smul_ne_zero hk0 hφ₂0
  have hψc : (k • φ₂) ⬝ᵥ c = 0 := by
    rw [hk, dotProduct_smul, smul_eq_mul] at hφ₂d₂
    rw [smul_dotProduct, smul_eq_mul]
    exact hφ₂d₂
  have hφψ : ∀ μ : K, φ ≠ μ • (k • φ₂) := fun μ h => by
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at h
      exact hφ h
    apply hg₂φ (μ * k)⁻¹
    rw [h, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ (mul_ne_zero hμ0 hk0), one_smul]
  exact false_of_two_tv hT ht₂T ht₁T ht₂' ht₁' hc hψ0 hψc he₁0 hφ hφe₁ he₁c hφψ

variable [Finite K]

theorem sl_wc (hm : 3 ≤ m) {T : Subgroup SL(m, K)} (hT : IsWC T) (hT1 : T ≠ ⊥) :
    (∃ c : Fin m → K, c ≠ 0 ∧ T = tvCenterSL c) ∨ (∃ a : Fin m → K, a ≠ 0 ∧ T = tvAxisSL a) := by
  obtain ⟨t₀, ht₀T, c, φ, hc, hφ, hφc, ht₀⟩ := exists_tv_mem_of_isWC hm hT hT1
  have ht₀1 : t₀ ≠ 1 := by
    rintro rfl
    apply vecMulVec_ne_zero_of hc hφ
    rw [Matrix.SpecialLinearGroup.coe_one] at ht₀
    have := congrArg (fun M => M - 1) ht₀
    simpa using this.symm
  have hfix : ∀ {x : SL(m, K)}, x ∈ T →
      (x : Matrix (Fin m) (Fin m) K) *ᵥ c = c ∧ φ ᵥ* (x : Matrix (Fin m) (Fin m) K) = φ :=
    fun hx => fix_of_commute_tv hc hφ ht₀ (elemAbelian_mul_comm hT.1 hx ht₀T)
      (elemAbelian_mul_self hT.1 hx)
  rcases sl_wc_dichotomy hT ht₀T hc hφ hφc ht₀ with h | h
  · refine Or.inl ⟨c, hc, hT.eq_of_le_of_transitive (fun x hx => ?_) tvCenterSL_comm ht₀T ht₀1
      (tvCenterSL_transitive hc hφ hφc ht₀)⟩
    choose μ hμ using h x hx
    set a : Fin m → K := fun j => μ (Pi.single j 1) with ha
    have hX : (x : Matrix (Fin m) (Fin m) K) - 1 = vecMulVec c a := by
      ext i j
      have := congrFun (hμ (Pi.single j 1)) i
      rw [mulVec_single_one] at this
      simpa [vecMulVec_apply, ha, mul_comm] using this
    refine ⟨a, ?_, by rw [← hX]; abel⟩
    have h2 : ((x : Matrix (Fin m) (Fin m) K) - 1) *ᵥ c = 0 := by
      rw [sub_mulVec, one_mulVec, (hfix hx).1, sub_self]
    rw [hX, vecMulVec_mulVec'] at h2
    exact (smul_eq_zero.1 h2).resolve_right hc
  · refine Or.inr ⟨φ, hφ, hT.eq_of_le_of_transitive (fun x hx => ?_) tvAxisSL_comm ht₀T ht₀1
      (tvAxisSL_transitive hc hφ hφc ht₀)⟩
    choose μ hμ using h x hx
    set v : Fin m → K := fun i => μ (Pi.single i 1) with hv
    have hX : (x : Matrix (Fin m) (Fin m) K) - 1 = vecMulVec v φ := by
      ext i j
      have := congrFun (hμ (Pi.single i 1)) j
      rw [single_one_vecMul] at this
      simpa [vecMulVec_apply, hv] using this
    refine ⟨v, ?_, by rw [← hX]; abel⟩
    have h2 : φ ᵥ* ((x : Matrix (Fin m) (Fin m) K) - 1) = 0 := by
      rw [vecMul_sub, vecMul_one, (hfix hx).2, sub_self]
    rw [hX, vecMul_vecMulVec] at h2
    exact (smul_eq_zero.1 h2).resolve_right hφ

end CFSG.CGT.Timmesfeld75
