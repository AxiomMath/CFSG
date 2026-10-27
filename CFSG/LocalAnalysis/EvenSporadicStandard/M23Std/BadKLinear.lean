module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NoLift4
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Matrix

theorem castHom_eq_of_two_mul_eq (x : ZMod 4) (y : ZMod 2)
    (h : 2 * x = 2 * ((y.val : ℕ) : ZMod 4)) :
    ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) x = y := by
  revert x y
  decide

theorem no_bad_pair {V : Type*} [AddCommGroup V] [Module (ZMod 4) V]
    (e : V ≃ₗ[ZMod 4] (Fin 4 → ZMod 4)) (r₁ r₂ : V →ₗ[ZMod 4] V)
    (h₁ : ∀ v, r₁ (r₁ v) = v) (h₂ : ∀ v, r₂ (r₂ v) = v) (h₁₂ : ∀ v, r₁ (r₂ v) = r₂ (r₁ v))
    (hm₁ : ∀ k i, 2 * e (r₁ (e.symm (Pi.single k 1))) i = 2 * (((liftA1 k i).val : ℕ) : ZMod 4))
    (hm₂ : ∀ k i, 2 * e (r₂ (e.symm (Pi.single k 1))) i = 2 * (((liftA2 k i).val : ℕ) : ZMod 4)) :
    False := by
  let ψ₁ : Module.End (ZMod 4) (Fin 4 → ZMod 4) := e.toLinearMap ∘ₗ r₁ ∘ₗ e.symm.toLinearMap
  let ψ₂ : Module.End (ZMod 4) (Fin 4 → ZMod 4) := e.toLinearMap ∘ₗ r₂ ∘ₗ e.symm.toLinearMap
  have hψ₁ : ψ₁ * ψ₁ = 1 := by
    ext v i
    simp [ψ₁, h₁]
  have hψ₂ : ψ₂ * ψ₂ = 1 := by
    ext v i
    simp [ψ₂, h₂]
  have hψ₁₂ : (ψ₁ * ψ₂) * (ψ₁ * ψ₂) = 1 := by
    ext v i
    simp [ψ₁, ψ₂, h₁₂, h₁, h₂]
  have hM₁ : LinearMap.toMatrix' ψ₁ * LinearMap.toMatrix' ψ₁ = 1 := by
    rw [← LinearMap.toMatrix'_mul, hψ₁]
    simp
  have hM₂ : LinearMap.toMatrix' ψ₂ * LinearMap.toMatrix' ψ₂ = 1 := by
    rw [← LinearMap.toMatrix'_mul, hψ₂]
    simp
  have hM₁₂ : (LinearMap.toMatrix' ψ₁ * LinearMap.toMatrix' ψ₂) *
      (LinearMap.toMatrix' ψ₁ * LinearMap.toMatrix' ψ₂) = 1 := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_mul, hψ₁₂]
    simp
  refine no_lift4_transpose (LinearMap.toMatrix' ψ₁) (LinearMap.toMatrix' ψ₂) ?_ ?_ hM₁ hM₂ hM₁₂
  · ext i k
    simp only [Matrix.map_apply, Matrix.transpose_apply, LinearMap.toMatrix'_apply]
    apply castHom_eq_of_two_mul_eq
    have := hm₁ k i
    simpa [ψ₁, Pi.single_apply] using this
  · ext i k
    simp only [Matrix.map_apply, Matrix.transpose_apply, LinearMap.toMatrix'_apply]
    apply castHom_eq_of_two_mul_eq
    have := hm₂ k i
    simpa [ψ₂, Pi.single_apply] using this

theorem no_bad_pair_group {Λ : Type*} [CommGroup Λ] (y : Fin 4 → Λ) (hexp : ∀ a : Λ, a ^ 4 = 1)
    (hgen : ∀ a : Λ, ∃ c : Fin 4 → ZMod 4, a = ∏ i, y i ^ (c i).val)
    (hind : ∀ c c' : Fin 4 → ZMod 4,
      ∏ i, y i ^ (c i).val = ∏ i, y i ^ (c' i).val → c = c')
    (ρ₁ ρ₂ : Λ →* Λ) (h₁ : ∀ a, ρ₁ (ρ₁ a) = a) (h₂ : ∀ a, ρ₂ (ρ₂ a) = a)
    (h₁₂ : ∀ a, ρ₁ (ρ₂ a) = ρ₂ (ρ₁ a))
    (hm₁ : ∀ k, ρ₁ (y k) ^ 2 = ∏ i, (y i ^ 2) ^ (liftA1 k i).val)
    (hm₂ : ∀ k, ρ₂ (y k) ^ 2 = ∏ i, (y i ^ 2) ^ (liftA2 k i).val) : False := by
  let _ : Module (ZMod 4) (Additive Λ) := AddCommGroup.zmodModule (fun a =>
    Additive.toMul.injective (by rw [toMul_nsmul, hexp, toMul_zero]))
  let Φ : (Fin 4 → ZMod 4) →ₗ[ZMod 4] Additive Λ :=
    Fintype.linearCombination (ZMod 4) (fun i => Additive.ofMul (y i))
  have hΦ : ∀ c, Φ c = Additive.ofMul (∏ i, y i ^ (c i).val) := by
    intro c
    simp only [Φ, Fintype.linearCombination_apply, ofMul_prod, ofMul_pow]
    rfl
  have hΦinj : Function.Injective Φ := by
    intro c c' hcc
    rw [hΦ, hΦ] at hcc
    exact hind c c' (Additive.ofMul.injective hcc)
  have hΦsurj : Function.Surjective Φ := by
    intro v
    obtain ⟨c, hc⟩ := hgen (Additive.toMul v)
    exact ⟨c, by rw [hΦ, ← hc]; rfl⟩
  let eqv : (Fin 4 → ZMod 4) ≃ₗ[ZMod 4] Additive Λ := LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  let e : Additive Λ ≃ₗ[ZMod 4] (Fin 4 → ZMod 4) := eqv.symm
  have he' : ∀ v, Φ (e v) = v := fun v => eqv.apply_symm_apply v
  have hsymm : ∀ c, e.symm c = Φ c := fun c => rfl
  let r₁ : Additive Λ →ₗ[ZMod 4] Additive Λ := (MonoidHom.toAdditive ρ₁).toZModLinearMap 4
  let r₂ : Additive Λ →ₗ[ZMod 4] Additive Λ := (MonoidHom.toAdditive ρ₂).toZModLinearMap 4
  have hr₁ : ∀ a : Λ, r₁ (Additive.ofMul a) = Additive.ofMul (ρ₁ a) := fun a => rfl
  have hr₂ : ∀ a : Λ, r₂ (Additive.ofMul a) = Additive.ofMul (ρ₂ a) := fun a => rfl
  have hsingle : ∀ k, Φ (Pi.single k 1) = Additive.ofMul (y k) := by
    intro k
    rw [hΦ]
    congr 1
    rw [Finset.prod_eq_single k]
    · have h1 : (1 : ZMod 4).val = 1 := rfl
      simp [h1]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have key : ∀ (ρ : Λ →* Λ) (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
      (hm : ∀ k, ρ (y k) ^ 2 = ∏ i, (y i ^ 2) ^ (A k i).val) (k i : Fin 4),
      2 * e (Additive.ofMul (ρ (y k))) i = 2 * (((A k i).val : ℕ) : ZMod 4) := by
    intro ρ A hm k i
    have hL : Φ (2 • e (Additive.ofMul (ρ (y k)))) =
        Additive.ofMul (∏ i, (y i ^ 2) ^ (A k i).val) := by
      rw [map_nsmul, he', ← hm k, ofMul_pow]
    have hR : Φ (fun i => ((2 * (A k i).val : ℕ) : ZMod 4)) =
        Additive.ofMul (∏ i, (y i ^ 2) ^ (A k i).val) := by
      simp only [Φ, Fintype.linearCombination_apply, Nat.cast_smul_eq_nsmul]
      rw [ofMul_prod]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← pow_mul, ofMul_pow]
    have h2 := congrFun (hΦinj (hL.trans hR.symm)) i
    simpa using h2
  have hi₁ : ∀ a : Λ, r₁ (r₁ (Additive.ofMul a)) = Additive.ofMul a := fun a => by
    rw [hr₁, hr₁, h₁]
  have hi₂ : ∀ a : Λ, r₂ (r₂ (Additive.ofMul a)) = Additive.ofMul a := fun a => by
    rw [hr₂, hr₂, h₂]
  have hi₁₂ : ∀ a : Λ, r₁ (r₂ (Additive.ofMul a)) = r₂ (r₁ (Additive.ofMul a)) := fun a => by
    rw [hr₁, hr₂, hr₁, hr₂, h₁₂]
  refine no_bad_pair e r₁ r₂ (fun v => hi₁ (Additive.toMul v)) (fun v => hi₂ (Additive.toMul v))
    (fun v => hi₁₂ (Additive.toMul v)) (fun k i => ?_) (fun k i => ?_)
  · rw [hsymm, hsingle, hr₁]
    exact key ρ₁ liftA1 hm₁ k i
  · rw [hsymm, hsingle, hr₂]
    exact key ρ₂ liftA2 hm₂ k i

end CFSG.EvenSporadicStandard.M23Std
