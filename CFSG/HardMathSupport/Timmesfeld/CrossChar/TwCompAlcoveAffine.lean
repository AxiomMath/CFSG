module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

@[expose] def alcoveValue {r : ℕ} (p : ℕ) (μ γ : Fin r → ℤ) : ℤ :=
  γ ⬝ᵥ μ + if ∀ j, 0 ≤ γ j then 0 else (p : ℤ)

namespace KacData

variable {τ : Tag} (K : KacData τ)

private theorem single_nonneg (j : Fin τ.rank) :
    ∀ k, 0 ≤ (Pi.single j 1 : Fin τ.rank → ℤ) k := by
  intro k
  by_cases h : k = j
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h]

private theorem not_nonneg_neg_theta : ¬ ∀ j, 0 ≤ (-K.θ : Fin τ.rank → ℤ) j := by
  intro h
  apply K.isRoot_θ.ne_zero
  funext j
  simp only [Pi.zero_apply]
  have h1 := h j
  have h2 := K.θ_nonneg j
  simp only [Pi.neg_apply] at h1
  linarith

theorem alcoveValue_extRoot_none (hK : K.Facts) (p : ℕ) (μ : Fin τ.rank → ℤ) :
    alcoveValue p μ (K.extRoot none) = p - K.θ ⬝ᵥ μ := by
  have hne : ¬ ∀ j, 0 ≤ (K.extRoot none : Fin τ.rank → ℤ) j := by
    have _ := hK.θ_pos
    simpa [extRoot] using not_nonneg_neg_theta (K := K)
  rw [alcoveValue, if_neg hne, extRoot, neg_dotProduct]
  ring

theorem alcoveValue_extRoot_some (p : ℕ) (μ : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    alcoveValue p μ (K.extRoot (some j)) = μ j := by
  have hnn : ∀ k, 0 ≤ (K.extRoot (some j) : Fin τ.rank → ℤ) k := by
    simpa [extRoot] using single_nonneg j
  rw [alcoveValue, if_pos hnn, extRoot, single_dotProduct, one_mul, add_zero]

private theorem not_nonneg_neg_of_nonneg {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hpos : ∀ j, 0 ≤ γ j) : ¬ ∀ j, 0 ≤ (-γ : Fin τ.rank → ℤ) j := by
  intro h
  apply hγ.ne_zero
  funext j
  simp only [Pi.zero_apply]
  have h1 := h j
  have h2 := hpos j
  simp only [Pi.neg_apply] at h1
  linarith

theorem alcoveValue_add_neg (p : ℕ) (μ : Fin τ.rank → ℤ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : alcoveValue p μ γ + alcoveValue p μ (-γ) = p := by
  by_cases hpos : ∀ j, 0 ≤ γ j
  · have hneg : ¬ ∀ j, 0 ≤ (-γ : Fin τ.rank → ℤ) j := not_nonneg_neg_of_nonneg hγ hpos
    rw [alcoveValue, if_pos hpos, alcoveValue, if_neg hneg, neg_dotProduct]
    ring
  · have hneg : ∀ j, 0 ≤ (-γ : Fin τ.rank → ℤ) j := by
      rcases IsRoot.nonneg_or_nonpos hγ with h | h
      · exact absurd h hpos
      · intro j
        simpa using h j
    rw [alcoveValue, if_neg hpos, alcoveValue, if_pos hneg, neg_dotProduct]
    ring

private theorem dotProduct_nonneg {γ μ : Fin τ.rank → ℤ} (hγ : ∀ j, 0 ≤ γ j)
    (hμ : ∀ j, 0 ≤ μ j) : 0 ≤ γ ⬝ᵥ μ :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hγ j) (hμ j)

private theorem dotProduct_le_theta (hK : K.Facts) {p : ℕ} {μ : Fin τ.rank → ℤ}
    (hμ : K.IsNormal p μ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγ0 : ∀ j, 0 ≤ γ j) :
    γ ⬝ᵥ μ ≤ K.θ ⬝ᵥ μ :=
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hK.le_θ γ hγ hγ0 j) (hμ.1 j)

private theorem dotProduct_bounds (hK : K.Facts) {p : ℕ} {μ : Fin τ.rank → ℤ}
    (hμ : K.IsNormal p μ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγ0 : ∀ j, 0 ≤ γ j) :
    0 ≤ γ ⬝ᵥ μ ∧ γ ⬝ᵥ μ ≤ p :=
  ⟨dotProduct_nonneg hγ0 hμ.1, (dotProduct_le_theta (K := K) hK hμ hγ hγ0).trans hμ.2⟩

private theorem alcoveValue_bounds (hK : K.Facts) {p : ℕ} {μ : Fin τ.rank → ℤ}
    (hμ : K.IsNormal p μ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    0 ≤ alcoveValue p μ γ ∧ alcoveValue p μ γ ≤ p := by
  rcases IsRoot.nonneg_or_nonpos hγ with hpos | hneg
  · obtain ⟨h0, hle⟩ := dotProduct_bounds (K := K) hK hμ hγ hpos
    have hv : alcoveValue p μ γ = γ ⬝ᵥ μ := by rw [alcoveValue, if_pos hpos, add_zero]
    rw [hv]
    exact ⟨h0, hle⟩
  · have hpos' : ∀ j, 0 ≤ (-γ) j := fun j => by simpa using hneg j
    obtain ⟨h0, hle⟩ := dotProduct_bounds (K := K) hK hμ (IsRoot.neg hγ) hpos'
    have hvneg : alcoveValue p μ (-γ) = (-γ) ⬝ᵥ μ := by
      rw [alcoveValue, if_pos hpos', add_zero]
    have hsum := alcoveValue_add_neg p μ hγ
    rw [hvneg] at hsum
    constructor <;> linarith

theorem alcoveValue_nonneg (hK : K.Facts) {p : ℕ} {μ : Fin τ.rank → ℤ} (hμ : K.IsNormal p μ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : 0 ≤ alcoveValue p μ γ := by
  exact (alcoveValue_bounds (K := K) hK hμ hγ).1

theorem alcoveValue_le (hK : K.Facts) {p : ℕ} {μ : Fin τ.rank → ℤ} (hμ : K.IsNormal p μ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : alcoveValue p μ γ ≤ p := by
  exact (alcoveValue_bounds (K := K) hK hμ hγ).2

private theorem alcoveValue_sub_dot (p : ℕ) (μ γ : Fin τ.rank → ℤ) :
    alcoveValue p μ γ - γ ⬝ᵥ μ = (p : ℤ) * (if ∀ j, 0 ≤ γ j then 0 else 1) := by
  rw [alcoveValue]
  by_cases h : ∀ j, 0 ≤ γ j
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring

private theorem alcoveValue_add_sub (p : ℕ) (μ x y : Fin τ.rank → ℤ) :
    alcoveValue p μ (x + y) - alcoveValue p μ x - alcoveValue p μ y =
      (p : ℤ) * ((if ∀ j, 0 ≤ (x + y) j then 0 else 1) -
        (if ∀ j, 0 ≤ x j then 0 else 1) - (if ∀ j, 0 ≤ y j then 0 else 1)) := by
  have h1 := alcoveValue_sub_dot p μ (x + y)
  have h2 := alcoveValue_sub_dot p μ x
  have h3 := alcoveValue_sub_dot p μ y
  rw [add_dotProduct] at h1
  linear_combination h1 - h2 - h3

private theorem alcoveValue_add_eq_iff {p : ℕ} (hp : 0 < p) (μ x y : Fin τ.rank → ℤ) :
    alcoveValue p μ (x + y) = alcoveValue p μ x + alcoveValue p μ y ↔
      (if ∀ j, 0 ≤ (x + y) j then (0 : ℤ) else 1) =
        (if ∀ j, 0 ≤ x j then 0 else 1) + (if ∀ j, 0 ≤ y j then 0 else 1) := by
  have h := alcoveValue_add_sub p μ x y
  constructor
  · intro he
    have hz : (p : ℤ) * ((if ∀ j, 0 ≤ (x + y) j then 0 else 1) -
        (if ∀ j, 0 ≤ x j then 0 else 1) - (if ∀ j, 0 ≤ y j then 0 else 1)) = 0 := by
      linarith
    rcases mul_eq_zero.1 hz with hp0 | h0
    · have : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
      exact absurd hp0 this
    · linarith
  · intro he
    rw [he] at h
    linarith

private theorem eq_or_cases_of_dvd_bounds {p : ℕ} {A B : ℤ}
    (hA : 0 ≤ A ∧ A ≤ (p : ℤ)) (hB : 0 ≤ B ∧ B ≤ (p : ℤ))
    (hdiv : (p : ℤ) ∣ A - B) :
    A = B ∨ (A = 0 ∧ B = (p : ℤ)) ∨ (A = (p : ℤ) ∧ B = 0) := by
  by_cases hAB : A = B
  · exact Or.inl hAB
  · right
    obtain ⟨k, hk⟩ := hdiv
    have hd0 : A - B ≠ 0 := sub_ne_zero.2 hAB
    have hp0 : (p : ℤ) ≠ 0 := by
      intro h
      apply hd0
      rw [hk, h, zero_mul]
    have hppos : (0 : ℤ) < p := lt_of_le_of_ne (by exact_mod_cast Nat.zero_le p) (Ne.symm hp0)
    have hk_le : k ≤ 1 := by nlinarith [hA.2, hB.1, hk, hppos]
    have hk_ge : -1 ≤ k := by nlinarith [hA.1, hB.2, hk, hppos]
    have hk_ne : k ≠ 0 := by
      intro h
      apply hd0
      rw [hk, h]
      ring
    have hk_cases : k = 1 ∨ k = -1 := by omega
    rcases hk_cases with hk1 | hk1
    · right
      constructor
      · rw [hk1] at hk
        linarith [hA.2, hB.1]
      · rw [hk1] at hk
        linarith
    · left
      constructor
      · rw [hk1] at hk
        linarith [hB.2, hA.1]
      · rw [hk1] at hk
        linarith

theorem alcoveValue_map_eq (hK : K.Facts) {p : ℕ} {μ : Fin τ.rank → ℤ} (hμ : K.IsNormal p μ)
    (f : (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ)) (hf : ∀ γ, IsRoot τ γ → IsRoot τ (f γ))
    (hdvd : ∀ γ, IsRoot τ γ → (p : ℤ) ∣ f γ ⬝ᵥ μ - γ ⬝ᵥ μ)
    (hzero : ∀ γ, IsRoot τ γ → alcoveValue p μ γ = 0 → alcoveValue p μ (f γ) = 0) :
    ∀ γ, IsRoot τ γ → alcoveValue p μ (f γ) = alcoveValue p μ γ := by
  intro γ hγ
  have hbγ := alcoveValue_bounds (K := K) hK hμ hγ
  have hbf := alcoveValue_bounds (K := K) hK hμ (hf γ hγ)
  have hdiv : (p : ℤ) ∣ alcoveValue p μ (f γ) - alcoveValue p μ γ := by
    have h1 := alcoveValue_sub_dot p μ (f γ)
    have h2 := alcoveValue_sub_dot p μ γ
    have hd := hdvd γ hγ
    have hdiff : alcoveValue p μ (f γ) - alcoveValue p μ γ =
        (f γ ⬝ᵥ μ - γ ⬝ᵥ μ) +
          (p : ℤ) * ((if ∀ j, 0 ≤ (f γ) j then (0 : ℤ) else 1) -
            (if ∀ j, 0 ≤ γ j then (0 : ℤ) else 1)) := by
      linarith
    rw [hdiff]
    exact dvd_add hd ⟨_, rfl⟩
  rcases eq_or_cases_of_dvd_bounds hbf hbγ hdiv with h | ⟨hA0, hBp⟩ | ⟨hAp, hB0⟩
  · exact h
  · by_cases hpz : p = 0
    · rw [hA0, hBp, hpz]
      norm_num
    · exfalso
      have hpz' : (p : ℤ) ≠ 0 := by exact_mod_cast hpz
      have hppos : (0 : ℤ) < p :=
        lt_of_le_of_ne (by exact_mod_cast Nat.zero_le p) (Ne.symm hpz')
      have hneg : alcoveValue p μ (-γ) = 0 := by
        have := alcoveValue_add_neg p μ hγ
        linarith
      have hz := hzero (-γ) (IsRoot.neg hγ) hneg
      rw [map_neg f γ] at hz
      have hadd := alcoveValue_add_neg p μ (hf γ hγ)
      linarith [hz, hA0, hadd, hppos]
  · by_cases hpz : p = 0
    · rw [hAp, hB0, hpz]
      norm_num
    · exfalso
      have hpz' : (p : ℤ) ≠ 0 := by exact_mod_cast hpz
      have hppos : (0 : ℤ) < p :=
        lt_of_le_of_ne (by exact_mod_cast Nat.zero_le p) (Ne.symm hpz')
      have hA0' := hzero γ hγ hB0
      linarith [hA0', hAp, hppos]

private def Decomposable (p : ℕ) (μ : Fin τ.rank → ℤ) (γ : Fin τ.rank → ℤ) : Prop :=
  ∃ ε₁ ε₂ : Fin τ.rank → ℤ, IsRoot τ ε₁ ∧ IsRoot τ ε₂ ∧ γ = ε₁ + ε₂ ∧
    alcoveValue p μ γ = alcoveValue p μ ε₁ + alcoveValue p μ ε₂

private theorem indicator_nonneg (z : Fin τ.rank → ℤ) :
    0 ≤ (if ∀ j, 0 ≤ z j then (0 : ℤ) else 1) := by
  by_cases h : ∀ j, 0 ≤ z j <;> simp [h]

private theorem indicator_eq_zero_iff (z : Fin τ.rank → ℤ) :
    (if ∀ j, 0 ≤ z j then (0 : ℤ) else 1) = 0 ↔ ∀ j, 0 ≤ z j := by
  by_cases h : ∀ j, 0 ≤ z j <;> simp [h]

private theorem indicator_eq_one_iff (z : Fin τ.rank → ℤ) :
    (if ∀ j, 0 ≤ z j then (0 : ℤ) else 1) = 1 ↔ ¬ ∀ j, 0 ≤ z j := by
  by_cases h : ∀ j, 0 ≤ z j <;> simp [h]

private theorem indicator_eq_zero_or_one (z : Fin τ.rank → ℤ) :
    (if ∀ j, 0 ≤ z j then (0 : ℤ) else 1) = 0 ∨
      (if ∀ j, 0 ≤ z j then (0 : ℤ) else 1) = 1 := by
  by_cases h : ∀ j, 0 ≤ z j
  · left
    rw [if_pos h]
  · right
    rw [if_neg h]

private theorem nonpos_of_indicator_eq_one {z : Fin τ.rank → ℤ} (hz : IsRoot τ z)
    (h : (if ∀ j, 0 ≤ z j then (0 : ℤ) else 1) = 1) : ∀ j, z j ≤ 0 := by
  have hnot := (indicator_eq_one_iff z).1 h
  rcases IsRoot.nonneg_or_nonpos hz with h' | h'
  · exact absurd h' hnot
  · exact h'

private theorem not_nonpos_add_nonneg_eq_negTheta (hK : K.Facts) {x y : Fin τ.rank → ℤ}
    (hx : IsRoot τ x) (hy : IsRoot τ y) (hx0 : ∀ j, 0 ≤ x j) (hy0 : ∀ j, y j ≤ 0)
    (hsum : x + y = -K.θ) : False := by
  have hxne : x ≠ 0 := hx.ne_zero
  obtain ⟨j, hj⟩ : ∃ j, 0 < x j := by
    by_contra h
    push Not at h
    exact hxne (funext fun j => le_antisymm (h j) (hx0 j))
  have hle := hK.le_θ (-y) (IsRoot.neg hy) (fun k => by
    have h := hy0 k
    simp only [Pi.neg_apply]
    linarith) j
  have hval : (-y) j = K.θ j + x j := by
    have h := congrFun hsum j
    simp only [Pi.add_apply, Pi.neg_apply] at h
    simp only [Pi.neg_apply]
    linarith
  have hpos := hK.θ_pos j
  linarith

private theorem not_decomposable_extRoot_some {p : ℕ} (hp : 0 < p) {μ : Fin τ.rank → ℤ}
    (j : Fin τ.rank) : ¬ Decomposable p μ (K.extRoot (some j)) := by
  rintro ⟨ε₁, ε₂, h₁, h₂, hsum, hval⟩
  have hI := (alcoveValue_add_eq_iff hp μ ε₁ ε₂).1 (by
    rw [hsum] at hval
    exact hval)
  have hIsum : (if ∀ k, 0 ≤ (ε₁ + ε₂) k then (0 : ℤ) else 1) = 0 := by
    rw [← hsum, if_pos (by simpa [extRoot] using single_nonneg j)]
  have hI12 : (if ∀ k, 0 ≤ ε₁ k then (0 : ℤ) else 1) +
      (if ∀ k, 0 ≤ ε₂ k then (0 : ℤ) else 1) = 0 := by
    linarith
  have hI1 : (if ∀ k, 0 ≤ ε₁ k then (0 : ℤ) else 1) = 0 := by
    have h1' := indicator_nonneg ε₁
    have h2' := indicator_nonneg ε₂
    linarith
  have hI2 : (if ∀ k, 0 ≤ ε₂ k then (0 : ℤ) else 1) = 0 := by
    have h1' := indicator_nonneg ε₁
    have h2' := indicator_nonneg ε₂
    linarith
  have hnn1 := (indicator_eq_zero_iff ε₁).1 hI1
  have hnn2 := (indicator_eq_zero_iff ε₂).1 hI2
  have hht : height (K.extRoot (some j)) = 1 := by
    simp [extRoot]
  have hadd := height_add ε₁ ε₂
  rw [← hsum, hht] at hadd
  have h1n : 0 ≤ height ε₁ := Finset.sum_nonneg fun k _ => hnn1 k
  have h2n : 0 ≤ height ε₂ := Finset.sum_nonneg fun k _ => hnn2 k
  have h1z := h₁.height_ne_zero
  have h2z := h₂.height_ne_zero
  omega

private theorem not_decomposable_extRoot_none (hK : K.Facts) {p : ℕ} (hp : 0 < p)
    {μ : Fin τ.rank → ℤ} : ¬ Decomposable p μ (K.extRoot none) := by
  rintro ⟨ε₁, ε₂, h₁, h₂, hsum, hval⟩
  have hI := (alcoveValue_add_eq_iff hp μ ε₁ ε₂).1 (by
    rw [hsum] at hval
    exact hval)
  have hIsum : (if ∀ k, 0 ≤ (ε₁ + ε₂) k then (0 : ℤ) else 1) = 1 := by
    rw [← hsum, if_neg]
    simpa [extRoot] using not_nonneg_neg_theta (K := K)
  have hI12 : (if ∀ k, 0 ≤ ε₁ k then (0 : ℤ) else 1) +
      (if ∀ k, 0 ≤ ε₂ k then (0 : ℤ) else 1) = 1 := by
    linarith
  have hsum' : ε₁ + ε₂ = -K.θ := by simpa [extRoot] using hsum.symm
  rcases indicator_eq_zero_or_one ε₁ with h1 | h1 <;>
    rcases indicator_eq_zero_or_one ε₂ with h2 | h2
  · linarith
  · have hx := (indicator_eq_zero_iff ε₁).1 h1
    have hy := nonpos_of_indicator_eq_one h₂ h2
    exact not_nonpos_add_nonneg_eq_negTheta (K := K) hK h₁ h₂ hx hy hsum'
  · have hx := (indicator_eq_zero_iff ε₂).1 h2
    have hy := nonpos_of_indicator_eq_one h₁ h1
    exact not_nonpos_add_nonneg_eq_negTheta (K := K) hK h₂ h₁ hx hy (by rw [add_comm]; exact hsum')
  · linarith

private theorem not_decomposable_extRoot (hK : K.Facts) {p : ℕ} (hp : 0 < p)
    {μ : Fin τ.rank → ℤ} (x : Option (Fin τ.rank)) :
    ¬ Decomposable p μ (K.extRoot x) := by
  cases x with
  | none => exact not_decomposable_extRoot_none (K := K) hK hp
  | some j => exact not_decomposable_extRoot_some (K := K) hp j

private theorem decomposable_of_not_extRoot (hK : K.Facts)
    (hup : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → γ ≠ K.θ →
      ∃ j, IsRoot τ (γ + Pi.single j 1))
    (hdown : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → (∀ j, γ ≠ Pi.single j 1) →
      ∃ j, IsRoot τ (γ - Pi.single j 1) ∧ ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin τ.rank → ℤ) k)
    {p : ℕ} (hp : 0 < p) {μ : Fin τ.rank → ℤ} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hne : ∀ x, γ ≠ K.extRoot x) : Decomposable p μ γ := by
  have _ := hK.θ_pos
  rcases IsRoot.nonneg_or_nonpos hγ with hpos | hneg
  · have hnot : ∀ j, γ ≠ Pi.single j 1 :=
      fun j h => hne (some j) (by simpa [extRoot] using h)
    obtain ⟨j, hroot, hnn⟩ := hdown γ hγ hpos hnot
    refine ⟨γ - Pi.single j 1, Pi.single j 1, hroot, IsRoot.basis j, ?_, ?_⟩
    · abel
    · have hγeq : γ = (γ - Pi.single j 1) + Pi.single j 1 := by abel
      conv_lhs => rw [hγeq]
      refine (alcoveValue_add_eq_iff hp μ (γ - Pi.single j 1) (Pi.single j 1)).2 ?_
      have h1 : (if ∀ k, 0 ≤ γ k then (0 : ℤ) else 1) = 0 := by rw [if_pos hpos]
      have h2 : (if ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin τ.rank → ℤ) k then (0 : ℤ) else 1) = 0 := by
        rw [if_pos hnn]
      have h3 : (if ∀ k, 0 ≤ (Pi.single j 1 : Fin τ.rank → ℤ) k then (0 : ℤ) else 1) = 0 := by
        rw [if_pos (single_nonneg j)]
      rw [← hγeq, h1, h2, h3]
      ring
  · have hγnot : ¬ ∀ j, 0 ≤ γ j := by
      intro h
      exact hγ.ne_zero (funext fun k => le_antisymm (hneg k) (h k))
    have hneθ : -γ ≠ K.θ := by
      intro h
      exact hne none (by simpa [extRoot] using (neg_eq_iff_eq_neg).mp h)
    obtain ⟨j, hβ⟩ := hup (-γ) (IsRoot.neg hγ) (fun k => by simpa using hneg k) hneθ
    set x := -(-γ + Pi.single j 1) with hxdef
    have hxeq : x = γ - Pi.single j 1 := by rw [hxdef]; abel
    have hxnot : ¬ ∀ k, 0 ≤ x k := by
      rw [hxeq]
      intro h
      have h1 := h j
      have h2 := hneg j
      simp only [Pi.sub_apply, Pi.single_eq_same] at h1
      linarith
    refine ⟨x, Pi.single j 1, hxdef ▸ IsRoot.neg hβ, IsRoot.basis j, ?_, ?_⟩
    · rw [hxeq]
      abel
    · have hγeq : γ = x + Pi.single j 1 := by rw [hxeq]; abel
      conv_lhs => rw [hγeq]
      refine (alcoveValue_add_eq_iff hp μ x (Pi.single j 1)).2 ?_
      have h1 : (if ∀ k, 0 ≤ γ k then (0 : ℤ) else 1) = 1 := by rw [if_neg hγnot]
      have h2 : (if ∀ k, 0 ≤ x k then (0 : ℤ) else 1) = 1 := by rw [if_neg hxnot]
      have h3 : (if ∀ k, 0 ≤ (Pi.single j 1 : Fin τ.rank → ℤ) k then (0 : ℤ) else 1) = 0 := by
        rw [if_pos (single_nonneg j)]
      rw [← hγeq, h1, h2, h3]
      ring

private theorem decomposable_map {p : ℕ} {μ : Fin τ.rank → ℤ}
    (f : (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ))
    (hf : ∀ γ, IsRoot τ (f γ) ↔ IsRoot τ γ)
    (hv : ∀ γ, IsRoot τ γ → alcoveValue p μ (f γ) = alcoveValue p μ γ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hdec : Decomposable p μ γ) :
    Decomposable p μ (f γ) := by
  obtain ⟨ε₁, ε₂, h₁, h₂, hsum, hval⟩ := hdec
  refine ⟨f ε₁, f ε₂, (hf ε₁).mpr h₁, (hf ε₂).mpr h₂, ?_, ?_⟩
  · rw [hsum, map_add]
  · rw [hv γ hγ, hval, hv ε₁ h₁, hv ε₂ h₂]

private theorem exists_extRoot_of_not_decomposable (hK : K.Facts)
    (hup : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → γ ≠ K.θ →
      ∃ j, IsRoot τ (γ + Pi.single j 1))
    (hdown : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → (∀ j, γ ≠ Pi.single j 1) →
      ∃ j, IsRoot τ (γ - Pi.single j 1) ∧ ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin τ.rank → ℤ) k)
    {p : ℕ} (hp : 0 < p) {μ : Fin τ.rank → ℤ} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hnd : ¬ Decomposable p μ γ) : ∃ x, γ = K.extRoot x := by
  by_contra h
  push Not at h
  exact hnd (decomposable_of_not_extRoot (K := K) hK hup hdown hp hγ h)

private theorem extRoot_injective : Function.Injective K.extRoot := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some j =>
      exfalso
      apply not_nonneg_neg_theta (K := K)
      have h2 : (-K.θ : Fin τ.rank → ℤ) = Pi.single j 1 := by simpa [extRoot] using h
      intro k
      rw [h2]
      exact single_nonneg j k
  | some j =>
    cases y with
    | none =>
      exfalso
      apply not_nonneg_neg_theta (K := K)
      have h2 : (Pi.single j 1 : Fin τ.rank → ℤ) = -K.θ := by simpa [extRoot] using h
      intro k
      rw [← h2]
      exact single_nonneg j k
    | some k =>
      have h2 : (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single k 1 := by
        simpa [extRoot] using h
      by_contra hjk
      have hjk' : j ≠ k := fun h => hjk (by rw [h])
      have hj := congrFun h2 j
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hjk'] at hj
      exact one_ne_zero hj

theorem exists_perm_extRoot_of_alcoveValue (hK : K.Facts)
    (hup : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → γ ≠ K.θ →
      ∃ j, IsRoot τ (γ + Pi.single j 1))
    (hdown : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → (∀ j, γ ≠ Pi.single j 1) →
      ∃ j, IsRoot τ (γ - Pi.single j 1) ∧ ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin τ.rank → ℤ) k)
    {p : ℕ} (hp : 0 < p) {μ : Fin τ.rank → ℤ}
    (f : (Fin τ.rank → ℤ) ≃ₗ[ℤ] (Fin τ.rank → ℤ)) (hf : ∀ γ, IsRoot τ (f γ) ↔ IsRoot τ γ)
    (hv : ∀ γ, IsRoot τ γ → alcoveValue p μ (f γ) = alcoveValue p μ γ) :
    ∃ σ : Equiv.Perm (Option (Fin τ.rank)), ∀ x, f (K.extRoot x) = K.extRoot (σ x) := by
  classical
  have hf_symm : ∀ γ, IsRoot τ (f.symm γ) ↔ IsRoot τ γ := by
    intro γ
    have h := hf (f.symm γ)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hv_symm : ∀ γ, IsRoot τ γ → alcoveValue p μ (f.symm γ) = alcoveValue p μ γ := by
    intro γ hγ
    have hδ : IsRoot τ (f.symm γ) := (hf_symm γ).mpr hγ
    have h := hv (f.symm γ) hδ
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hmap : ∀ x : Option (Fin τ.rank), ∃ y, f (K.extRoot x) = K.extRoot y := by
    intro x
    have hroot : IsRoot τ (f (K.extRoot x)) := (hf (K.extRoot x)).mpr (K.isRoot_extRoot x)
    refine exists_extRoot_of_not_decomposable (K := K) (μ := μ) hK hup hdown hp hroot ?_
    intro hdec
    have hback : Decomposable p μ (f.symm (f (K.extRoot x))) :=
      decomposable_map (f.symm : (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ))
        hf_symm hv_symm hroot hdec
    rw [LinearEquiv.symm_apply_apply] at hback
    exact not_decomposable_extRoot (K := K) hK hp x hback
  let g : Option (Fin τ.rank) → Option (Fin τ.rank) := fun x => Classical.choose (hmap x)
  have hg : ∀ x, f (K.extRoot x) = K.extRoot (g x) := fun x => Classical.choose_spec (hmap x)
  have hinj : Function.Injective g := by
    intro x y hxy
    apply extRoot_injective (K := K)
    apply f.injective
    rw [hg x, hg y, hxy]
  have hbij : Function.Bijective g :=
    ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  refine ⟨Equiv.ofBijective g hbij, ?_⟩
  intro x
  exact hg x

end KacData

end CFSG.HardMathSupport.Timmesfeld.CrossChar

end
