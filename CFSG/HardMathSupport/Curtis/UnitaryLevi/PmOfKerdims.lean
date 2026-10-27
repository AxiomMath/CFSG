module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SemilinearPm
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

open scoped Classical in
theorem pm_of_kerdims (hK : Nat.card K = 4)
    (Et : Subgroup (LinearMap.GeneralLinearGroup K V)) (χ : Fin 3 → (Et →* Kˣ))
    (hinj : ∀ e : Et, (∀ i, χ i e = 1) → e = 1) (d : Fin 3 → ℕ)
    (hd : ∀ S T : Finset (Fin 3), ∑ i ∈ S, d i = ∑ i ∈ T, d i → S = T)
    (hker : ∀ (e : Et) (lam : Kˣ),
      Module.finrank K (LinearMap.ker (((e : LinearMap.GeneralLinearGroup K V) :
        Module.End K V) - (lam : K) • 1)) = ∑ i, d i * (if χ i e = lam then 1 else 0))
    (φ : K ≃+* K) (τ : V ≃+ V) (hτ : ∀ c v, τ (c • v) = φ c • τ v)
    (e e' : Et)
    (hee' : ∀ v, ((e' : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (τ v) =
      τ (((e : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v)) :
    e' = e ∨ e' = e⁻¹ := by
  classical
  have hsum : ∀ (a : Et) (lam : Kˣ), Module.finrank K (LinearMap.ker (((a :
      LinearMap.GeneralLinearGroup K V) : Module.End K V) - (lam : K) • 1)) =
      ∑ i ∈ Finset.univ.filter (fun i => χ i a = lam), d i := by
    intro a lam
    rw [hker a lam, Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have hiff : ∀ i, ((χ i e' : Kˣ) : K) = φ ((χ i e : Kˣ) : K) := by
    intro i
    have hne : φ ((χ i e : Kˣ) : K) ≠ 0 := by
      rw [map_ne_zero_iff _ φ.injective]; exact (χ i e).ne_zero
    set lam' : Kˣ := Units.mk0 _ hne with hlam'
    have hdimeq := finrank_eigenspace_eq φ τ hτ
      ((e : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
      ((e' : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) hee' ((χ i e : Kˣ) : K)
    rw [Module.End.eigenspace_def, Module.End.eigenspace_def] at hdimeq
    have h1 := hsum e (χ i e)
    have h2 := hsum e' lam'
    have hlam'v : (lam' : K) = φ ((χ i e : Kˣ) : K) := rfl
    rw [← hlam'v] at hdimeq
    rw [h1, h2] at hdimeq
    have hST := hd _ _ hdimeq
    have hi : i ∈ Finset.univ.filter (fun j => χ j e = χ i e) := by simp
    rw [hST] at hi
    have : χ i e' = lam' := by simpa using hi
    rw [this]
    exact hlam'v
  have key : ∀ a b : Et, (∀ i, χ i a = χ i b) → a = b := by
    intro a b h
    have := hinj (a⁻¹ * b) (fun i => by simp [h i])
    exact inv_mul_eq_one.mp this
  by_cases hφ : φ = 1
  · left
    apply key
    intro i
    apply Units.ext
    rw [hiff i, hφ]
    rfl
  · right
    apply key
    intro i
    apply Units.ext
    have h3 := units_pow_three_eq_one_of_card_four hK (χ i e)
    rw [hiff i, ringEquiv_apply_eq_sq_of_card_four hK hφ, map_inv, Units.val_inv_eq_inv_val]
    have : (χ i e : Kˣ) ^ 2 = (χ i e)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, h3]
    simpa using congrArg Units.val this

end CFSG.HardMathSupport.Curtis.UnitaryLevi
