module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.QuasithinUnique.AppC

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem exists_even_perm_moving_four : ∀ x : Fin 5, ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ σ 4 = x := by
  decide +kernel

theorem stab_prod_three : ∀ h : Perm (Fin 5), Perm.sign h = 1 → h 4 = 4 →
    ∃ c₁ c₂ : Perm (Fin 5), Perm.sign c₁ = 1 ∧ c₁ 4 = 4 ∧ c₁ ^ 3 = 1 ∧
      Perm.sign c₂ = 1 ∧ c₂ 4 = 4 ∧ c₂ ^ 3 = 1 ∧ h = c₁ * c₂ := by
  decide +kernel

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

theorem zmod2_three_mul (x : ZMod 2) : x + x + x = x := by
  revert x; decide

theorem cocycle_coboundary {Γ : Type*} [Group Γ] (ρ : Γ →* Perm (Fin 5))
    (hρ : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∃ γ, ρ γ = σ)
    (hρev : ∀ γ, Perm.sign (ρ γ) = 1)
    (W : Γ → (Fin 5 → ZMod 2))
    (hW : ∀ a b, W (a * b) = W a + pact (ρ a) (W b)) (hker : ∀ k, ρ k = 1 → W k = 0) :
    ∃ w₀ : Fin 5 → ZMod 2, isEven w₀ ∧ ∀ γ, W γ = pact (ρ γ) w₀ + w₀ := by
  classical
  have hW1 : W 1 = 0 := hker 1 (map_one ρ)
  have hWinv : ∀ γ, W γ⁻¹ = pact (ρ γ)⁻¹ (W γ) := by
    intro γ
    have h := hW γ⁻¹ γ
    rw [inv_mul_cancel, hW1] at h
    rw [map_inv] at h
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    generalize W γ⁻¹ i = p at hi ⊢
    generalize pact (ρ γ)⁻¹ (W γ) i = q at hi ⊢
    revert p q; decide
  have hstab : ∀ t, ρ t 4 = 4 → W t 4 = 0 := by
    intro t ht
    obtain ⟨c₁, c₂, hs1, h41, h31, hs2, h42, h32, hc⟩ :=
      stab_prod_three (ρ t) (hρev t) ht
    obtain ⟨γ₁, hγ₁⟩ := hρ c₁ hs1
    obtain ⟨γ₂, hγ₂⟩ := hρ c₂ hs2
    have hcub : ∀ γ : Γ, ρ γ 4 = 4 → (ρ γ) ^ 3 = 1 → W γ 4 = 0 := by
      intro γ h4 h3
      have hk : W (γ ^ 3) = 0 := hker _ (by rw [map_pow]; exact h3)
      have e2 : W (γ ^ 2) = W γ + pact (ρ γ) (W γ) := by
        rw [pow_two, hW]
      have e3 : W (γ ^ 3) = W γ + pact (ρ γ) (W (γ ^ 2)) := by
        rw [pow_succ', hW]
      rw [e3, e2] at hk
      have hk4 := congrFun hk 4
      have hinv4 : (ρ γ)⁻¹ 4 = 4 := by
        rw [Perm.inv_def, Equiv.symm_apply_eq]; exact h4.symm
      simp only [Pi.add_apply, pact, hinv4, Pi.zero_apply] at hk4
      have hkk : W γ 4 + (W γ 4 + W γ 4) = 0 := by
        convert hk4 using 2
      have := zmod2_three_mul (W γ 4)
      rw [← add_assoc] at hkk
      rw [this] at hkk
      exact hkk
    have h1 : W γ₁ 4 = 0 := hcub γ₁ (by rw [hγ₁]; exact h41) (by rw [hγ₁]; exact h31)
    have h2 : W γ₂ 4 = 0 := hcub γ₂ (by rw [hγ₂]; exact h42) (by rw [hγ₂]; exact h32)
    set k := (γ₁ * γ₂)⁻¹ * t with hk
    have hkker : ρ k = 1 := by
      rw [hk, map_mul, map_inv, map_mul, hγ₁, hγ₂, ← hc]; simp
    have htk : t = γ₁ * γ₂ * k := by rw [hk]; group
    have hWt : W t = W (γ₁ * γ₂) := by
      rw [htk, hW, hker k hkker]
      funext i
      show W (γ₁ * γ₂) i + 0 = W (γ₁ * γ₂) i
      exact add_zero _
    rw [hWt, hW]
    have hinv4 : (ρ γ₁)⁻¹ 4 = 4 := by
      rw [Perm.inv_def, Equiv.symm_apply_eq]; rw [hγ₁]; exact h41.symm
    simp only [Pi.add_apply, pact, hinv4]
    rw [h1, h2]; decide
  have hmove : ∀ x : Fin 5, ∃ γ : Γ, ρ γ 4 = x := by
    intro x
    obtain ⟨σ, hσ, hσx⟩ := exists_even_perm_moving_four x
    obtain ⟨γ, hγ⟩ := hρ σ hσ
    exact ⟨γ, by rw [hγ]; exact hσx⟩
  choose g hg using hmove
  set a : Fin 5 → ZMod 2 := fun x => W (g x) x with ha
  have hax : ∀ x, a x = W (g x)⁻¹ 4 := by
    intro x
    rw [hWinv]
    simp only [pact, ha]
    rw [inv_inv, hg x]
  have key : ∀ γ x, W γ x = a x + a ((ρ γ)⁻¹ x) := by
    intro γ x
    set y := (ρ γ)⁻¹ x with hy
    set t := (g x)⁻¹ * γ * g y with ht
    have hρt : ρ t 4 = 4 := by
      rw [ht, map_mul, map_mul, map_inv, Perm.mul_apply, Perm.mul_apply, hg y, hy]
      show (ρ (g x)).symm ((ρ γ) ((ρ γ)⁻¹ x)) = 4
      have hx : (ρ γ) ((ρ γ)⁻¹ x) = x := by simp
      rw [hx]
      exact (Equiv.symm_apply_eq (ρ (g x))).2 (hg x).symm
    have h0 := hstab t hρt
    have e1 : W t 4 = W (g x)⁻¹ 4 + W (γ * g y) x := by
      rw [ht, mul_assoc, hW]
      simp only [Pi.add_apply, pact]
      rw [map_inv, inv_inv, hg x]
    have e2 : W (γ * g y) x = W γ x + a y := by
      rw [hW]
      simp only [Pi.add_apply, pact]
      rfl
    rw [e1, e2, ← hax] at h0
    have h3 : W γ x = a x + a y := by
      have := h0
      revert this
      generalize W γ x = c
      generalize a x = p
      generalize a y = q
      revert c p q; decide
    exact h3
  set c : ZMod 2 := ∑ i, a i with hc
  set w₀ : Fin 5 → ZMod 2 := fun i => a i + c with hw₀
  refine ⟨w₀, ?_, fun γ => ?_⟩
  · show ∑ i, (a i + c) = 0
    rw [Finset.sum_add_distrib, ← hc]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h5 : ∀ r : ZMod 2, (5 : ℕ) • r = r := by decide
    rw [h5 c]
    exact zmod2_add_self c
  · funext x
    simp only [Pi.add_apply]
    show W γ x = a ((ρ γ)⁻¹ x) + c + (a x + c)
    rw [key γ x]
    generalize a x = p
    generalize a ((ρ γ)⁻¹ x) = q
    generalize c = r
    revert p q r; decide

end CFSG.QuasithinUnique.AppC
