module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHThetaAux

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Permutation.SymmetricCoxeter

structure FyThetaData {G : Type*} [Group G] (f yr r : G) (x : ℕ → G) : Prop where
  f4 : f ^ 4 = 1
  t_ne : f ^ 2 ≠ 1
  yr_sq : yr * yr = 1
  yr_f : yr * f * yr⁻¹ = f⁻¹
  r3 : r ^ 3 = 1
  r_ne : r ≠ 1
  r_f : r * f = f * r
  r_yr : r * yr = yr * r
  r_x : ∀ i < 4, r * x i = x i * r
  f_x : ∀ i < 4, f * x i = x i * f
  yr_x : ∀ i < 4, yr * x i = x i * yr
  cox : IsCoxeterA 4 x
  x01 : x 0 * x 1 ≠ 1

open ThetaHom

theorem FyThetaData.exists_hom {G : Type*} [Group G] {f yr r : G} {x : ℕ → G}
    (h : FyThetaData f yr r x) :
    ∃ Θ : HModel →* G, Function.Injective Θ ∧
      (∀ k : ZMod 4, Θ (DihedralGroup.r k, 1, 1) = f ^ k.val) ∧
      (∀ k : ZMod 4, Θ (DihedralGroup.sr k, 1, 1) = (f ^ k.val)⁻¹ * yr) ∧
      (∀ c : Z3, Θ (1, c, 1) = r ^ (Multiplicative.toAdd c).val) ∧
      (∀ i < 4, Θ (1, 1, adjSwap 4 i) = x i) := by
  obtain ⟨ΘS, hΘS⟩ := exists_hom_perm 4 x h.cox
  let ΘD := dihHom h.f4 h.yr_sq h.yr_f
  let ΘZ := zmodPow 3 r h.r3
  have hZc : ∀ g : G, Commute r g → ∀ c, Commute (ΘZ c) g := fun g hg c => by
    rw [zmodPow_apply]
    exact hg.pow_left _
  have h3 : ∀ c σ, Commute (ΘZ c) (ΘS σ) := fun c σ => hZc _ (commute_perm hΘS h.r_x σ) c
  have h2 : ∀ d σ, Commute (ΘD d) (ΘS σ) := fun d σ =>
    (commute_dihHom (commute_perm hΘS h.f_x σ).symm (commute_perm hΘS h.yr_x σ).symm d).symm
  have h1 : ∀ d c, Commute (ΘD d) (ΘZ c) := fun d c =>
    (commute_dihHom (hZc f (show r * f = f * r from h.r_f) c)
      (hZc yr (show r * yr = yr * r from h.r_yr) c) d).symm
  obtain ⟨Θ, hΘ⟩ := exists_prod_hom ΘD ΘZ ΘS h1 h2 h3
  have hS : Function.Injective ΘS := by
    refine perm_five_injective ΘS ?_
    rw [map_mul, hΘS 0 (by norm_num), hΘS 1 (by norm_num)]
    exact h.x01
  have hD : Function.Injective ΘD := by
    rw [injective_iff_map_eq_one]
    intro a ha
    by_contra hne
    have hr2 : ΘD (DihedralGroup.r 2) = f ^ 2 := by
      rw [dihHom_r]
      rfl
    refine h.t_ne ?_
    rw [← hr2]
    rcases (by decide : ∀ a : DihedralGroup 4, a ≠ 1 → a = DihedralGroup.r 2 ∨
        a * a = DihedralGroup.r 2 ∨ ∃ g : DihedralGroup 4,
          a * (g * a⁻¹ * g⁻¹) = DihedralGroup.r 2) a hne with e | e | ⟨g, e⟩
    · rw [← e, ha]
    · rw [← e, map_mul, ha, mul_one]
    · rw [← e, map_mul, map_mul, map_mul, map_inv, map_inv, ha]
      simp
  have hZ : Function.Injective ΘZ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    rcases (by decide : ∀ c : Z3, c = 1 ∨ c = Multiplicative.ofAdd 1 ∨
        c = Multiplicative.ofAdd 2) c with rfl | rfl | rfl
    · rfl
    · exfalso
      refine h.r_ne ?_
      have e : r ^ (1 : ZMod 3).val = 1 := hc
      have e1 : (1 : ZMod 3).val = 1 := by decide
      rwa [e1, pow_one] at e
    · exfalso
      refine h.r_ne ?_
      have e : r ^ (2 : ZMod 3).val = 1 := hc
      have e2 : (2 : ZMod 3).val = 2 := by decide
      rw [e2] at e
      calc r = r ^ 3 * (r ^ 2)⁻¹ := by group
        _ = 1 := by rw [h.r3, e, inv_one, mul_one]
  refine ⟨Θ, prod_hom_injective Θ ΘD ΘZ ΘS hΘ h2 h3 hD hZ hS, fun k => ?_, fun k => ?_,
    fun c => ?_, fun i hi => ?_⟩
  · rw [hΘ, map_one, map_one, mul_one, mul_one]
    exact dihHom_r h.f4 h.yr_sq h.yr_f k
  · rw [hΘ, map_one, map_one, mul_one, mul_one]
    exact dihHom_sr h.f4 h.yr_sq h.yr_f k
  · rw [hΘ, map_one, map_one, one_mul, mul_one]
    exact zmodPow_apply 3 r h.r3 c
  · rw [hΘ, map_one, map_one, one_mul, one_mul]
    exact hΘS i hi

theorem FyThetaData.theta_r_two {G : Type*} [Group G] {f : G} (Θ : HModel →* G)
    (hΘ : ∀ k : ZMod 4, Θ (DihedralGroup.r k, 1, 1) = f ^ k.val) :
    Θ (DihedralGroup.r 2, 1, 1) = f ^ 2 := by
  rw [hΘ]
  rfl

theorem FyThetaData.theta_v0 {G : Type*} [Group G] {x : ℕ → G} (Θ : HModel →* G)
    (hΘ : ∀ i < 4, Θ (1, 1, adjSwap 4 i) = x i) : Θ (1, 1, v0) = x 0 * x 2 := by
  have hv : v0 = adjSwap 4 0 * adjSwap 4 2 := by
    rw [adjSwap_of_lt (by norm_num), adjSwap_of_lt (by norm_num)]
    rfl
  have hm : ((1 : DihedralGroup 4), (1 : Z3), v0) =
      ((1 : DihedralGroup 4), (1 : Z3), adjSwap 4 0) *
        ((1 : DihedralGroup 4), (1 : Z3), adjSwap 4 2) := by
    rw [hv]
    simp
  rw [hm, map_mul, hΘ 0 (by norm_num), hΘ 2 (by norm_num)]

end CFSG.EvenSporadicStandard.TwoHS
