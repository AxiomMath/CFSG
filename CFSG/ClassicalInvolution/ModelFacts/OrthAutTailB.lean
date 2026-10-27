module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutOdd

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open CFSG.LieType.Universal.Spin

variable {K X : Type} [Group K] [Group X] {F : Type} [Field F] {p : ℕ} {W : Type}
  [AddCommGroup W] [Module F W] {m : ℕ}

omit [Module F W] in
theorem toral_tail_B (h2 : (2 : F) ≠ 0) (hZ : ∀ ζ ∈ Subgroup.center K, ζ ^ p = 1 → ζ = 1)
    (θ : K →* X) (hker : θ.ker ≤ Subgroup.center K) (σ : X ≃* X) (α A : K ≃* K) (κ : K)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) (hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹)
    (hA2 : ∀ y, A (A y) = y) (rootGroup : (Fin m → ℤ) → Subgroup K)
    (Lr : ∀ i j : Fin m, i ≠ j → Bool → Bool → Multiplicative F →* K)
    (Sr : Fin m → Bool → Multiplicative W →* K)
    (hLinj : ∀ i j (hij : i ≠ j) s t, Function.Injective (Lr i j hij s t))
    (hLp : ∀ i j (hij : i ≠ j) s t (c : F), (Lr i j hij s t (.ofAdd c)) ^ p = 1)
    (hSinj : ∀ i s, Function.Injective (Sr i s))
    (hSp : ∀ i s (w : W), (Sr i s (.ofAdd w)) ^ p = 1)
    (hlong : ∀ γ i j (hij : i ≠ j) s t,
      toStdB m γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) →
        rootGroup γ = (Lr i j hij s t).range)
    (hshort : ∀ γ i s, toStdB m γ = Pi.single i (boolSign s) → rootGroup γ = (Sr i s).range)
    (lam : Fin m → Bool → F) (μ ζ : F) (hμ : μ ≠ 0) (hζ2 : ζ * ζ = μ)
    (hprod : ∀ i, lam i true * lam i false = μ) (hlamsq : ∀ i s, lam i s * lam i s = μ)
    (hAlong : ∀ i j (hij : i ≠ j) s t (c : F), A (Lr i j hij s t (.ofAdd c)) =
      Lr i j hij s t (.ofAdd ((lam j t * (μ⁻¹ * lam i s)) * c)))
    (M : Fin m → Bool → W → W)
    (hAshort : ∀ i s (w : W), A (Sr i s (.ofAdd w)) = Sr i s (.ofAdd (M i s w)))
    (HS : Prop) (hM : ∀ i s, (∀ w, M i s w = w) ↔ (HS ∧ lam i s * (μ⁻¹ * ζ) = 1)) :
    ∃ v : Fin m → ZMod 2, ∀ γ : Fin m → ℤ,
      γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanB m) ∅ →
      ((((rootGroup γ ⊔ rootGroup (-γ)).map (MulAut.conj κ).toMonoidHom).map θ).map
          σ.toMonoidHom =
        ((rootGroup γ ⊔ rootGroup (-γ)).map (MulAut.conj κ).toMonoidHom).map θ) ∧
      ((∀ y ∈ ((rootGroup γ ⊔ rootGroup (-γ)).map (MulAut.conj κ).toMonoidHom).map θ,
          σ y = y) ↔
        (∑ i, (γ i : ZMod 2) * v i = 0 ∧
          ((∃ (i : Fin m) (s : Bool), toStdB m γ = Pi.single i (boolSign s)) → HS))) := by
  classical
  have hζ0 : ζ ≠ 0 := fun h0 => hμ (by rw [← hζ2, h0, zero_mul])
  have hlam2 : ∀ k s, lam k (!s) * lam k s = μ := by
    intro k s
    cases s
    · simpa using hprod k
    · simpa [mul_comm] using hprod k
  have hlam0 : ∀ k s, lam k s ≠ 0 := fun k s h0 => hμ (by rw [← hlam2 k s, h0, mul_zero])
  let a : Fin m → Fˣ := fun k => Units.mk0 (lam k true / ζ) (div_ne_zero (hlam0 k true) hζ0)
  have hlamζ : ∀ k s, lam k s = ζ * (a k : F) ^ boolSign s := by
    intro k s
    have h0 := hlam0 k true
    cases s
    · simp only [boolSign_false, a, Units.val_mk0, zpow_neg, zpow_one]
      have hp := hprod k
      rw [← hζ2] at hp
      field_simp
      linear_combination hp
    · simp only [boolSign_true, a, Units.val_mk0, zpow_one]
      field_simp
  have hasq : ∀ k, (a k : F) * (a k : F) = 1 := by
    intro k
    simp only [a, Units.val_mk0]
    have h0 := hlam0 k true
    have := hlamsq k true
    field_simp
    linear_combination this - hζ2
  have hψlong : ∀ (γ : Fin m → ℤ) (i j : Fin m) (s t : Bool),
      toStdB m γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) →
        ((charPsiB a (Multiplicative.ofAdd γ) : Fˣ) : F) = lam j t * (μ⁻¹ * lam i s) := by
    intro γ i j s t h
    rw [charPsiB_long a s t h, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_zpow_eq_zpow_val, hlamζ i s, hlamζ j t, ← hζ2]
    have hai : (a i : F) ≠ 0 := (a i).ne_zero
    have haj : (a j : F) ≠ 0 := (a j).ne_zero
    field_simp
  have hψshort : ∀ (γ : Fin m → ℤ) (i : Fin m) (s : Bool),
      toStdB m γ = Pi.single i (boolSign s) →
        ((charPsiB a (Multiplicative.ofAdd γ) : Fˣ) : F) = lam i s * (μ⁻¹ * ζ) := by
    intro γ i s h
    rw [charPsiB_short a s h, Units.val_zpow_eq_zpow_val, hlamζ i s, ← hζ2]
    have hai : (a i : F) ≠ 0 := (a i).ne_zero
    field_simp
  have hψ1 : ∀ a₀ : Fin m, charPsiB a (Multiplicative.ofAdd (Pi.single a₀ 1)) = 1 ∨
      charPsiB a (Multiplicative.ofAdd (Pi.single a₀ 1)) = -1 := by
    intro a₀
    by_cases hlt : a₀.val + 1 < m
    · have hrep : toStdB m (Pi.single a₀ 1) = Pi.single a₀ (boolSign true) +
          Pi.single (⟨a₀.val + 1, hlt⟩ : Fin m) (boolSign false) := by
        rw [toStdB_single_of_lt m hlt, boolSign_true, boolSign_false, Pi.single_neg,
          sub_eq_add_neg]
      have h1 := charPsiB_long a true false hrep
      have hx : ((charPsiB a (Multiplicative.ofAdd (Pi.single a₀ 1)) : Fˣ) : F) *
          ((charPsiB a (Multiplicative.ofAdd (Pi.single a₀ 1)) : Fˣ) : F) = 1 := by
        rw [h1, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
        have hi := hasq a₀
        have hj := hasq ⟨a₀.val + 1, hlt⟩
        have hai : (a a₀ : F) ≠ 0 := (a a₀).ne_zero
        have haj : (a ⟨a₀.val + 1, hlt⟩ : F) ≠ 0 := (a _).ne_zero
        simp only [boolSign_true, boolSign_false, zpow_one, zpow_neg]
        field_simp
        rw [sq, sq, hi, hj]
      rcases mul_self_eq_one_iff.mp hx with h3 | h3
      · exact Or.inl (Units.ext (by rw [h3, Units.val_one]))
      · exact Or.inr (Units.ext (by rw [h3, Units.val_neg, Units.val_one]))
    · have hrep : toStdB m (Pi.single a₀ 1) = Pi.single a₀ (boolSign true) := by
        rw [toStdB_single_of_not_lt m hlt, boolSign_true]
      have h1 := charPsiB_short a true hrep
      have hx : ((charPsiB a (Multiplicative.ofAdd (Pi.single a₀ 1)) : Fˣ) : F) *
          ((charPsiB a (Multiplicative.ofAdd (Pi.single a₀ 1)) : Fˣ) : F) = 1 := by
        rw [h1, Units.val_zpow_eq_zpow_val, boolSign_true, zpow_one]
        exact hasq a₀
      rcases mul_self_eq_one_iff.mp hx with h3 | h3
      · exact Or.inl (Units.ext (by rw [h3, Units.val_one]))
      · exact Or.inr (Units.ext (by rw [h3, Units.val_neg, Units.val_one]))
  obtain ⟨v, hv⟩ := exists_vec_of_hom h2 (charPsiB a) hψ1
  refine ⟨v, fun γ hγ => ?_⟩
  rcases odd_root_cases hγ with ⟨i, j, hij, s, t, hstd⟩ | ⟨i, s, hstd⟩
  · have hX1 : rootGroup γ = (Lr i j hij s t).range := hlong γ i j hij s t hstd
    have hstd' : toStdB m (-γ) = Pi.single i (boolSign (!s)) + Pi.single j (boolSign (!t)) := by
      have e : toStdB m (-γ) = -toStdB m γ := toStdB_neg m γ
      rw [e, hstd, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add]
    have hX2 : rootGroup (-γ) = (Lr i j hij (!s) (!t)).range := hlong (-γ) i j hij (!s) (!t) hstd'
    rw [hX1, hX2]
    have hχ : lam j t * (μ⁻¹ * lam i s) = 1 →
        lam j (!t) * (μ⁻¹ * lam i (!s)) = 1 := by
      intro h1
      have hprod' : (lam j (!t) * (μ⁻¹ * lam i (!s))) * (lam j t * (μ⁻¹ * lam i s)) = 1 := by
        calc _ = (lam j (!t) * lam j t) * (lam i (!s) * lam i s) * (μ⁻¹ * μ⁻¹) := by ring
          _ = μ * μ * (μ⁻¹ * μ⁻¹) := by rw [hlam2, hlam2]
          _ = 1 := by field_simp
      rw [h1, mul_one] at hprod'
      exact hprod'
    have hmain := normalizes_and_fixes_of_map hZ θ hker σ α A κ hαθ hA hA2 (Lr i j hij s t)
      (Lr i j hij (!s) (!t)) (hLinj i j hij s t) (fun c => hLp i j hij s t c)
      (fun c => (lam j t * (μ⁻¹ * lam i s)) * c) (fun c => (lam j (!t) * (μ⁻¹ * lam i (!s))) * c)
      (hAlong i j hij s t) (hAlong i j hij (!s) (!t)) (fun hh w => by rw [hχ (by simpa using hh 1), one_mul])
    refine ⟨hmain.1, ?_⟩
    have hnot : ¬ ∃ (i' : Fin m) (s' : Bool), toStdB m γ = Pi.single i' (boolSign s') := by
      rintro ⟨i', s', h'⟩
      rw [hstd] at h'
      exact absurd h'.symm (single_ne_single_add_single hij (boolSign_ne_zero s)
        (boolSign_ne_zero t))
    rw [hmain.2, ← hv γ]
    constructor
    · intro hh
      have h1 : lam j t * (μ⁻¹ * lam i s) = 1 := by simpa using hh 1
      refine ⟨?_, fun h => absurd h hnot⟩
      apply Units.ext
      rw [hψlong γ i j s t hstd, Units.val_one]
      exact h1
    · rintro ⟨h1, -⟩
      intro w
      have h3 : ((charPsiB a (Multiplicative.ofAdd γ) : Fˣ) : F) = 1 := by
        rw [h1, Units.val_one]
      rw [hψlong γ i j s t hstd] at h3
      rw [h3, one_mul]
  · have hX1 : rootGroup γ = (Sr i s).range := hshort γ i s hstd
    have hstd' : toStdB m (-γ) = Pi.single i (boolSign (!s)) := by
      have e : toStdB m (-γ) = -toStdB m γ := toStdB_neg m γ
      rw [e, hstd, boolSign_not, Pi.single_neg]
    have hX2 : rootGroup (-γ) = (Sr i (!s)).range := hshort (-γ) i (!s) hstd'
    rw [hX1, hX2]
    have hχ : ∀ s', lam i s' * (μ⁻¹ * ζ) * (lam i (!s') * (μ⁻¹ * ζ)) = 1 := by
      intro s'
      calc _ = (lam i s' * lam i (!s')) * (μ⁻¹ * μ⁻¹) * (ζ * ζ) := by ring
        _ = μ * (μ⁻¹ * μ⁻¹) * μ := by rw [mul_comm (lam i s'), hlam2, hζ2]
        _ = 1 := by field_simp
    have hmain := normalizes_and_fixes_of_map hZ θ hker σ α A κ hαθ hA hA2 (Sr i s)
      (Sr i (!s)) (hSinj i s) (fun w => hSp i s w) (M i s) (M i (!s)) (hAshort i s)
      (hAshort i (!s)) (fun hh => by
        have h1 := (hM i s).mp hh
        refine (hM i (!s)).mpr ⟨h1.1, ?_⟩
        have := hχ s
        rw [h1.2, one_mul] at this
        exact this)
    refine ⟨hmain.1, ?_⟩
    rw [hmain.2, hM i s, ← hv γ, Units.ext_iff, hψshort γ i s hstd, Units.val_one]
    constructor
    · rintro ⟨hHS, h1⟩
      exact ⟨h1, fun _ => hHS⟩
    · rintro ⟨h1, hHS⟩
      exact ⟨hHS ⟨i, s, hstd⟩, h1⟩

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
