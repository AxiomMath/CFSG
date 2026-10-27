module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Commutant
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Normalize
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.AutFixed

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Swap

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_eq_of_preservesFactors (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (hS : StdHyp σ)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (hBσ : ∀ g x y, B (σ g x) (σ g y) = B x y)
    (u : V ≃ₗ[ZMod 2] V) (hu : PreservesFactors σ u)
    (hα : u * σ (a₀, 1) = σ (a₀, 1) * u) (hβ : u * σ (1, a₀) = σ (1, a₀) * u)
    (hBu : ∀ x y, B (u x) (u y) = B x y) :
    ∃ g : A5 × A5, u = σ g := by
  have hmal : ∀ a b : A5, σ (a * b, (1 : A5)) = σ (a, 1) * σ (b, 1) := by
    intro a b
    rw [← map_mul]
    congr 1
  have hmal' : ∀ a b : A5, σ ((1 : A5), a * b) = σ ((1 : A5), a) * σ ((1 : A5), b) := by
    intro a b
    rw [← map_mul]
    congr 1
  let f₁ : A5 → A5 := fun x => Classical.choose (hu.1 x)
  have hf₁ : ∀ x : A5, u * σ (x, 1) * u⁻¹ = σ (f₁ x, 1) :=
    fun x => Classical.choose_spec (hu.1 x)
  have mul₁ : ∀ x y : A5, f₁ (x * y) = f₁ x * f₁ y := by
    intro x y
    have hp : (f₁ (x * y), (1 : A5)) = (f₁ x * f₁ y, (1 : A5)) := by
      apply hS.inj
      calc
        σ (f₁ (x * y), 1) = u * σ (x * y, 1) * u⁻¹ := (hf₁ (x * y)).symm
        _ = u * (σ (x, 1) * σ (y, 1)) * u⁻¹ := by rw [hmal x y]
        _ = (u * σ (x, 1) * u⁻¹) * (u * σ (y, 1) * u⁻¹) := by group
        _ = σ (f₁ x, 1) * σ (f₁ y, 1) := by rw [hf₁ x, hf₁ y]
        _ = σ (f₁ x * f₁ y, 1) := (hmal (f₁ x) (f₁ y)).symm
    simpa using congrArg Prod.fst hp
  let φ₁ : A5 →* A5 := MonoidHom.mk' f₁ mul₁
  have hφ₁ : ∀ x : A5, u * σ (x, 1) * u⁻¹ = σ (φ₁ x, 1) := fun x => hf₁ x
  have hφ₁a : φ₁ a₀ = a₀ := by
    have h : u * σ (a₀, 1) * u⁻¹ = σ (a₀, 1) := by
      rw [hα, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : σ (φ₁ a₀, 1) = σ (a₀, 1) := (hφ₁ a₀).symm.trans h
    exact congrArg Prod.fst (hS.inj h2)
  obtain ⟨i, hi⟩ := CFSG.EvenSporadicStandard.HNRecog.Fpf.exists_pow_conj_of_apply_eq φ₁ hφ₁a
  let f₂ : A5 → A5 := fun y => Classical.choose (hu.2 y)
  have hf₂ : ∀ y : A5, u * σ ((1 : A5), y) * u⁻¹ = σ ((1 : A5), f₂ y) :=
    fun y => Classical.choose_spec (hu.2 y)
  have mul₂ : ∀ x y : A5, f₂ (x * y) = f₂ x * f₂ y := by
    intro x y
    have hp : ((1 : A5), f₂ (x * y)) = ((1 : A5), f₂ x * f₂ y) := by
      apply hS.inj
      calc
        σ ((1 : A5), f₂ (x * y)) = u * σ ((1 : A5), x * y) * u⁻¹ := (hf₂ (x * y)).symm
        _ = u * (σ ((1 : A5), x) * σ ((1 : A5), y)) * u⁻¹ := by rw [hmal' x y]
        _ = (u * σ ((1 : A5), x) * u⁻¹) * (u * σ ((1 : A5), y) * u⁻¹) := by group
        _ = σ ((1 : A5), f₂ x) * σ ((1 : A5), f₂ y) := by rw [hf₂ x, hf₂ y]
        _ = σ ((1 : A5), f₂ x * f₂ y) := (hmal' (f₂ x) (f₂ y)).symm
    simpa using congrArg Prod.snd hp
  let φ₂ : A5 →* A5 := MonoidHom.mk' f₂ mul₂
  have hφ₂ : ∀ y : A5, u * σ ((1 : A5), y) * u⁻¹ = σ ((1 : A5), φ₂ y) := fun y => hf₂ y
  have hφ₂a : φ₂ a₀ = a₀ := by
    have h : u * σ ((1 : A5), a₀) * u⁻¹ = σ ((1 : A5), a₀) := by
      rw [hβ, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : σ ((1 : A5), φ₂ a₀) = σ ((1 : A5), a₀) := (hφ₂ a₀).symm.trans h
    exact congrArg Prod.snd (hS.inj h2)
  obtain ⟨j, hj⟩ := CFSG.EvenSporadicStandard.HNRecog.Fpf.exists_pow_conj_of_apply_eq φ₂ hφ₂a
  let g : A5 × A5 := (a₀ ^ i, a₀ ^ j)
  refine ⟨g, ?_⟩
  have hconj₁ : ∀ x : A5, σ (φ₁ x, 1) = σ g * σ (x, 1) * (σ g)⁻¹ := by
    intro x
    calc
      σ (φ₁ x, 1) = σ (a₀ ^ i * x * (a₀ ^ i)⁻¹, 1) := by rw [hi x]
      _ = σ g * σ (x, 1) * (σ g)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        ext <;> simp [g]
  have hconj₂ : ∀ y : A5,
      σ ((1 : A5), φ₂ y) = σ g * σ ((1 : A5), y) * (σ g)⁻¹ := by
    intro y
    calc
      σ ((1 : A5), φ₂ y) = σ ((1 : A5), a₀ ^ j * y * (a₀ ^ j)⁻¹) := by rw [hj y]
      _ = σ g * σ ((1 : A5), y) * (σ g)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        ext <;> simp [g]
  have hcomm₁ : ∀ x : A5,
      ((σ g)⁻¹ * u) * σ (x, 1) = σ (x, 1) * ((σ g)⁻¹ * u) := by
    intro x
    have hx : u * σ (x, 1) = σ (φ₁ x, 1) * u := by
      rw [← hφ₁ x]
      group
    calc
      ((σ g)⁻¹ * u) * σ (x, 1) = (σ g)⁻¹ * (u * σ (x, 1)) := by group
      _ = (σ g)⁻¹ * (σ (φ₁ x, 1) * u) := by rw [hx]
      _ = (σ g)⁻¹ * ((σ g * σ (x, 1) * (σ g)⁻¹) * u) := by rw [hconj₁ x]
      _ = σ (x, 1) * ((σ g)⁻¹ * u) := by group
  have hcomm₂ : ∀ y : A5,
      ((σ g)⁻¹ * u) * σ ((1 : A5), y) = σ ((1 : A5), y) * ((σ g)⁻¹ * u) := by
    intro y
    have hy : u * σ ((1 : A5), y) = σ ((1 : A5), φ₂ y) * u := by
      rw [← hφ₂ y]
      group
    calc
      ((σ g)⁻¹ * u) * σ ((1 : A5), y) = (σ g)⁻¹ * (u * σ ((1 : A5), y)) := by group
      _ = (σ g)⁻¹ * (σ ((1 : A5), φ₂ y) * u) := by rw [hy]
      _ = (σ g)⁻¹ * ((σ g * σ ((1 : A5), y) * (σ g)⁻¹) * u) := by rw [hconj₂ y]
      _ = σ ((1 : A5), y) * ((σ g)⁻¹ * u) := by group
  have hcomm : ∀ w : A5 × A5, ((σ g)⁻¹ * u) * σ w = σ w * ((σ g)⁻¹ * u) := by
    rintro ⟨x, y⟩
    have hxy : σ (x, y) = σ (x, 1) * σ ((1 : A5), y) := by
      rw [← map_mul]
      congr 1
    calc
      ((σ g)⁻¹ * u) * σ (x, y)
          = ((σ g)⁻¹ * u) * (σ (x, 1) * σ ((1 : A5), y)) := by rw [hxy]
      _ = (((σ g)⁻¹ * u) * σ (x, 1)) * σ ((1 : A5), y) := by group
      _ = (σ (x, 1) * ((σ g)⁻¹ * u)) * σ ((1 : A5), y) := by rw [hcomm₁ x]
      _ = σ (x, 1) * (((σ g)⁻¹ * u) * σ ((1 : A5), y)) := by group
      _ = σ (x, 1) * (σ ((1 : A5), y) * ((σ g)⁻¹ * u)) := by rw [hcomm₂ y]
      _ = (σ (x, 1) * σ ((1 : A5), y)) * ((σ g)⁻¹ * u) := by group
      _ = σ (x, y) * ((σ g)⁻¹ * u) := by rw [← hxy]
  have hBσinv : ∀ a b : V, B ((σ g)⁻¹ a) ((σ g)⁻¹ b) = B a b := by
    intro a b
    rw [← hBσ g ((σ g)⁻¹ a) ((σ g)⁻¹ b)]
    have ha : (σ g) ((σ g)⁻¹ a) = a := LinearEquiv.apply_symm_apply (σ g) a
    have hb : (σ g) ((σ g)⁻¹ b) = b := LinearEquiv.apply_symm_apply (σ g) b
    rw [ha, hb]
  have hBu' : ∀ a b : V, B (((σ g)⁻¹ * u) a) (((σ g)⁻¹ * u) b) = B a b := by
    intro a b
    simp only [LinearEquiv.mul_apply]
    rw [hBσinv (u a) (u b), hBu a b]
  have h1 : (σ g)⁻¹ * u = 1 :=
    eq_one_of_commute_of_isometry σ hS B hB hBσ ((σ g)⁻¹ * u) hcomm hBu'
  have h2 : σ g * ((σ g)⁻¹ * u) = σ g * 1 := by rw [h1]
  rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2
  exact h2

end CFSG.EvenSporadicStandard.HNRecog.Swap
