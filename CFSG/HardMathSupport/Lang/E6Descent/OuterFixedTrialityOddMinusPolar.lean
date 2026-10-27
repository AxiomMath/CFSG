module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddMinusCount
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddMinusBorel

public section

open scoped Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg Multiplicative

theorem un_final_card {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 0 < f)
    {X : Type*} [Group X] [Finite X] (D : RankTwoSystem X 3)
    (τ e : X ≃* X) (hτ : D.IsOpposition τ) (hτe : ∀ y, τ (τ y) = e y)
    (he : ∀ b ∈ D.B, e b ∈ D.B) (hτ4 : ∀ y, τ (τ (τ (τ y))) = y)
    {k : Type} [Field k] [Finite k] [CharP k p] (hk : Nat.card k = (p ^ f) ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ (p ^ f))
    (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* X) (hρinj : Function.Injective ρ) (κ : kˣ)
    (hu : ∀ a, τ (ρ (sl2Upper a)) = ρ (sl2Lower ((κ : k) * ε a)))
    (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (((κ⁻¹ : kˣ) : k) * ε a)))
    (hρ2 : ∀ a, ρ (sl2Upper a) ∈ D.root 2) (hρ2' : ∀ y ∈ D.root 2, ∃ a, y = ρ (sl2Upper a))
    (hρm2 : ∀ a, ρ (sl2Lower a) ∈ D.root (-2))
    (hρN : ∃ m₀ : D.N, (m₀ : X) = ρ unSL2W ∧ (m₀ : D.Weyl) = D.w₀)
    (hρH : ∀ u : kˣ, ρ (unSL2Diag u) ∈ D.B ⊓ D.N)
    (x₁ : Multiplicative k →* X) (hx₁inj : Function.Injective x₁)
    (hx₁ : ∀ a, x₁ a ∈ D.root 1) (hx₁s : ∀ y ∈ D.root 1, ∃ a, y = x₁ a)
    (hx₁torus : ∀ h ∈ D.B ⊓ D.N, ∃ χ : kˣ,
      ∀ a : k, h * x₁ (ofAdd a) * h⁻¹ = x₁ (ofAdd ((χ : k) * a)))
    (hx₁e : ∀ a : k, e (x₁ (ofAdd a)) = x₁ (ofAdd (ε (ε a))))
    (hab₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a)
    (hab₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a)
    (hTor : ∀ h ∈ D.B ⊓ D.N, ∀ y ∈ D.root 1, y ≠ 1 → ∀ z ∈ D.root 3, z ≠ 1 →
      h * y = y * h → h * z = z * h → h = 1)
    (hĉ : ∃ c ∈ D.B ⊓ D.N, τ c = c ∧ c * c = 1 ∧ ∀ y ∈ D.root (-2), c * y * c⁻¹ = y⁻¹) :
    ∃ m : ℕ, m ∣ (p ^ f) ^ 2 - 1 ∧
      Nat.card ↥(foldFix τ) = ((p ^ f) ^ 3 * m) * (1 + (p ^ f) ^ 3) := by
  obtain ⟨t, ht⟩ := un_norm_solution hf hk ε hε κ (un_norm_eq ρ hρinj τ hτ4 ε κ hu hl)
  have hg : (ρ (sl2Lower (t : k)))⁻¹ * τ (ρ (sl2Lower (t : k))) *
      ((D.lift D.w₀ : D.N) : X) ∈ D.B := un_adapted_mem_B D ρ τ ε κ hl hρ2 hρN hρH t ht
  have hθpol := hτ.isPolarity hg
  have hθapp := un_theta_apply τ (ρ (sl2Lower (t : k)))
  have hθ4 := un_theta_four τ hτ4 (ρ (sl2Lower (t : k)))
  obtain ⟨l₂, hθ₂⟩ := un_theta_x2 ρ τ ε κ hu hl t ht
  obtain ⟨ν, hθ₁₁⟩ := un_theta_sq_x1 D τ e hτ hτe he ε x₁ hx₁ hx₁torus hx₁e hab₁ hab₃ hg
  have hθ₁ := fun y (hy : y ∈ D.root 1) => hτ.theta_root₁ hg hy
  have hθ₃ := fun z (hz : z ∈ D.root 3) => hτ.theta_root₃ hg hz
  set x : X := ρ (sl2Lower (t : k))
  set θ : X ≃* X := τ.trans (MulAut.conj (x⁻¹ * τ x)) with hθdef
  have hx₂inj : Function.Injective (ρ.comp (unSL2UpperHom k)) := fun a b h =>
    Multiplicative.toAdd.injective
      (@un_sl2Upper_injective k _ (toAdd a) (toAdd b) (hρinj h))
  obtain ⟨hcard, -⟩ := un_heis_fixed D hp2 hf hk ε hε x₁ (ρ.comp (unSL2UpperHom k)) hx₁inj
    hx₂inj hx₁ (fun a => hρ2 _) hx₁s
    (fun y hy => by
      obtain ⟨a, ha⟩ := hρ2' y hy
      exact ⟨ofAdd a, ha⟩) hab₁ hab₃ θ hθpol.mem_U hθ4 l₂ ν hθ₂ hθ₁ hθ₃ hθ₁₁
  obtain ⟨c, hcH, hcτ, -, hcinv⟩ := hĉ
  have hc₀ := un_c0_mem_dc D ρ hρ2 hρm2 hρN hρH (un_two_ne_zero hp2) hcH hcinv t
  have hc₀f : θ (x⁻¹ * c * x) = x⁻¹ * c * x := by
    rw [hθapp]
    have e : x * (x⁻¹ * c * x) * x⁻¹ = c := by group
    rw [e, hcτ]
  have hcardθ := hθpol.card_foldFix hc₀ hc₀f
  have L : Layer1 D x₁ := ⟨hx₁inj, hx₁, hx₁torus, hab₁, hab₃, hTor⟩
  have hθ2 : ∀ y ∈ D.root 2, θ y ∈ D.root 2 := by
    intro y hy
    obtain ⟨a, rfl⟩ := hρ2' y hy
    have := hθ₂ a
    rw [this]
    exact hρ2 _
  have hθ2' : ∀ y, θ y ∈ D.root 2 → y ∈ D.root 2 := by
    intro y hy
    obtain ⟨a', ha'⟩ := hρ2' _ hy
    have hb : θ (ρ (sl2Upper (ε.symm (((l₂⁻¹ : kˣ) : k) * a')))) = θ y := by
      rw [hθ₂, ha']
      congr 3
      rw [RingEquiv.apply_symm_apply, ← mul_assoc]
      simp
    have := θ.injective hb
    rw [← this]
    exact hρ2 _
  have hN : ∀ c : kˣ, ε (ε (c : k)) = c → c ^ ((p ^ f) ^ 2 - 1) = 1 := by
    intro c hc
    rw [hε, hε] at hc
    have hq : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos (Fact.out : p.Prime).pos f)
    apply Units.ext
    have h1 : (c : k) ^ ((p ^ f) ^ 2) = c := by rw [pow_two, pow_mul]; exact hc
    have hc0 : (c : k) ≠ 0 := c.ne_zero
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    have h2 : (c : k) ^ ((p ^ f) ^ 2 - 1) * c = c := by
      rw [← pow_succ, Nat.sub_add_cancel hq]
      exact h1
    exact mul_right_cancel₀ hc0 (by rw [h2, one_mul])
  obtain ⟨m, hm, hBm⟩ := card_B_fix_dvd (ε := ε) (ν := ν) L hθ2 hθ2' hθ₁ hθ₁₁ _ hN
  refine ⟨m, hm, ?_⟩
  rw [hcard] at hBm
  have hXτ : Nat.card ↥(foldFix τ) = Nat.card ↥(foldFix θ) :=
    (Nat.card_congr (unFixEquiv τ θ x hθapp).toEquiv).symm
  rw [hXτ, hcardθ, hBm, hcard]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
