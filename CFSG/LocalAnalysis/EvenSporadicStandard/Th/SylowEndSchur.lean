module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.GL4Vanish

public section

namespace CFSG.EvenSporadicStandard.ThStd.SylowEnd

variable {G : Type*} [Group G]

theorem exists_pow_of_equivariant {A K D : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x ^ 2 = 1)
    (hcard : Nat.card A = 16)
    (surj : ∀ f : G → G, (∀ a ∈ A, f a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
      (∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b) → ∃ n ∈ K, ∀ a ∈ A, n * a * n⁻¹ = f a)
    (hAn : ∀ n ∈ K, (∀ a ∈ A, n * a * n⁻¹ ∈ A) → ∀ a ∈ A, n⁻¹ * a * n ∈ A)
    (hDn : ∀ n ∈ K, (∀ a ∈ A, n * a * n⁻¹ ∈ A) → ∀ d ∈ D, n * d * n⁻¹ ∈ D)
    (θ ρ : ↥D →* ↥A) (hθ : Function.Surjective θ) (hker : ∀ d, θ d = 1 → ρ d = 1)
    (hθK : ∀ n ∈ K, (∀ a ∈ A, n * a * n⁻¹ ∈ A) → ∀ (d : ↥D) (h : n * (d : G) * n⁻¹ ∈ D),
      ((θ ⟨n * d * n⁻¹, h⟩ : ↥A) : G) = n * (θ d : G) * n⁻¹)
    (hρK : ∀ n ∈ K, (∀ a ∈ A, n * a * n⁻¹ ∈ A) → ∀ (d : ↥D) (h : n * (d : G) * n⁻¹ ∈ D),
      ((ρ ⟨n * d * n⁻¹, h⟩ : ↥A) : G) = n * (ρ d : G) * n⁻¹)
    {a₀ : G} (ha₀ : a₀ ∈ A) (ha₀1 : a₀ ≠ 1) :
    ∃ e : ℕ, ∀ d : ↥D, ((ρ d : ↥A) : G) = ((θ d : ↥A) : G) ^ e := by
  classical
  let ρ' : G → G := fun a =>
    if h : a ∈ A then ((ρ (Classical.choose (hθ ⟨a, h⟩)) : ↥A) : G) else 1
  have hρ' : ∀ (d : ↥D) (a : G) (ha : a ∈ A), ((θ d : ↥A) : G) = a →
      ρ' a = ((ρ d : ↥A) : G) := by
    intro d a ha hda
    have hd₀ := Classical.choose_spec (hθ ⟨a, ha⟩)
    have h1 : θ ((Classical.choose (hθ ⟨a, ha⟩))⁻¹ * d) = 1 := by
      rw [map_mul, map_inv, hd₀]
      have : θ d = ⟨a, ha⟩ := Subtype.ext hda
      rw [this, inv_mul_cancel]
    have h2 := hker _ h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    simp only [ρ', dite_eq_left ha]
    exact congrArg (fun x : ↥A => (x : G)) h2
  have hD1 : ∀ a ∈ A, ρ' a ∈ A := by
    intro a ha
    simp only [ρ', dite_eq_left ha]
    exact (ρ _).2
  have hD2 : ∀ a ∈ A, ∀ b ∈ A, ρ' (a * b) = ρ' a * ρ' b := by
    intro a ha b hb
    obtain ⟨d₁, hd₁⟩ := hθ ⟨a, ha⟩
    obtain ⟨d₂, hd₂⟩ := hθ ⟨b, hb⟩
    have h1 : ((θ (d₁ * d₂) : ↥A) : G) = a * b := by
      rw [map_mul, hd₁, hd₂]
      rfl
    rw [hρ' _ _ (A.mul_mem ha hb) h1, hρ' d₁ a ha (congrArg Subtype.val hd₁),
      hρ' d₂ b hb (congrArg Subtype.val hd₂), map_mul]
    rfl
  have hconj : ∀ n ∈ K, (∀ a ∈ A, n * a * n⁻¹ ∈ A) → ∀ a ∈ A,
      ρ' (n * a * n⁻¹) = n * ρ' a * n⁻¹ := by
    intro n hn hnA a ha
    obtain ⟨d, hd⟩ := hθ ⟨a, ha⟩
    have hda : ((θ d : ↥A) : G) = a := congrArg Subtype.val hd
    have hnd : n * (d : G) * n⁻¹ ∈ D := hDn n hn hnA d d.2
    have h1 := hθK n hn hnA d hnd
    rw [hρ' ⟨n * d * n⁻¹, hnd⟩ (n * a * n⁻¹) (hnA a ha) (by rw [h1, hda]),
      hρK n hn hnA d hnd, hρ' d a ha hda]
  obtain ⟨e, he⟩ := endo_eq_pow_of_stabilizer hcomm hsq hcard surj ρ' hD1 hD2 ha₀ ha₀1
    (fun n hn hnA _ => ⟨0, fun a ha => by
      have h1 := hAn n hn hnA a ha
      have := hconj n hn hnA _ h1
      rw [show n * (n⁻¹ * a * n) * n⁻¹ = a by group] at this
      rw [this, pow_zero, mul_one]⟩)
  refine ⟨e, fun d => ?_⟩
  rw [← hρ' d _ (θ d).2 rfl]
  exact he _ (θ d).2

end CFSG.EvenSporadicStandard.ThStd.SylowEnd
