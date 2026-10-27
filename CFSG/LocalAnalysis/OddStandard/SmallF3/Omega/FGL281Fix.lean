module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGL281Aut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGL281Gal
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGL281Mat
import TauCeti.LinearAlgebra.Matrix.Commute

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter
open scoped commutatorElement

universe u

variable {K : Type u} [Field K]

theorem fg_twist_mat {M : Matrix.GeneralLinearGroup (Fin 2) K} {σ : K ≃+* K}
    {B : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : fgTwist M σ (Matrix.SpecialLinearGroup.toGL B) = Matrix.SpecialLinearGroup.toGL B) :
    (M : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K).map σ =
      (B : Matrix (Fin 2) (Fin 2) K) * M := by
  rw [fgTwist_apply, mul_inv_eq_iff_eq_mul] at h
  have h1 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K)) h
  have hmap : ((Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.toGL B) :
      Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (B : Matrix (Fin 2) (Fin 2) K).map σ :=
    Matrix.ext fun i j => by simp [Matrix.GeneralLinearGroup.map_apply]
  simpa [Units.val_mul, hmap] using h1

theorem fg_central_of_sigma_one {M : Matrix.GeneralLinearGroup (Fin 2) K}
    {P : Subgroup (PSL2 K)} (hP : ⁅P, P⁆ = P) (hne : P ≠ ⊥)
    (hfix : ∀ x ∈ P, semilinearAction K (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk M) *
        SemidirectProduct.inr 1) x = x) : Matrix.ProjGenLinGroup.mk M = 1 := by
  by_contra hM
  have hMs : (M : Matrix (Fin 2) (Fin 2) K) ∉ Set.range (Matrix.scalar (Fin 2)) := fun h =>
    hM (Matrix.ProjGenLinGroup.mk_eq_one.mpr
      (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr h))
  have hlift := fg_lift_fixed hP hfix
  refine hne ?_
  rw [← hP, eq_bot_iff, Subgroup.commutator_le]
  intro p hp q hq
  obtain ⟨B₁, rfl, h₁⟩ := hlift p hp
  obtain ⟨B₂, rfl, h₂⟩ := hlift q hq
  have c₁ : Commute (M : Matrix (Fin 2) (Fin 2) K) (B₁ : Matrix (Fin 2) (Fin 2) K) := by
    have h' : (M : Matrix (Fin 2) (Fin 2) K) * (B₁ : Matrix (Fin 2) (Fin 2) K) =
        (B₁ : Matrix (Fin 2) (Fin 2) K) * M := by simpa using fg_twist_mat h₁
    exact h'
  have c₂ : Commute (M : Matrix (Fin 2) (Fin 2) K) (B₂ : Matrix (Fin 2) (Fin 2) K) := by
    have h' : (M : Matrix (Fin 2) (Fin 2) K) * (B₂ : Matrix (Fin 2) (Fin 2) K) =
        (B₂ : Matrix (Fin 2) (Fin 2) K) * M := by simpa using fg_twist_mat h₂
    exact h'
  have c₁₂ := TauCeti.commute_of_commute_fin_two hMs c₁ c₂
  have hB : B₁ * B₂ = B₂ * B₁ := Subtype.ext (by simpa using c₁₂.eq)
  have h3 : ⁅(QuotientGroup.mk B₁ : PSL2 K), (QuotientGroup.mk B₂ : PSL2 K)⁆ =
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) ⁅B₁, B₂⁆ :=
    (map_commutatorElement (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) B₁ B₂).symm
  have : ⁅B₁, B₂⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hB
  rw [Subgroup.mem_bot, h3, this, map_one]

theorem fg_sq_of_fixes [Finite K] (hK : Nat.card K = 81)
    {M : Matrix.GeneralLinearGroup (Fin 2) K} {σ : K ≃+* K}
    {P : Subgroup (PSL2 K)} (hP : ⁅P, P⁆ = P) (hne : P ≠ ⊥)
    (hfix : ∀ x ∈ P, semilinearAction K (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk M) *
        SemidirectProduct.inr σ) x = x) : σ * σ = 1 := by
  by_contra hσ
  have hlift := fg_lift_fixed hP hfix
  refine hne (fg_eq_bot_of_pow_twelve hP fun x hx => ?_)
  obtain ⟨B, rfl, hB⟩ := hlift x hx
  have htr := fg_trace_eq_of_twisted M σ (fg_twist_mat hB)
  have hB12 : (B : Matrix (Fin 2) (Fin 2) K) ^ 12 = 1 :=
    fg_pow_twelve_of_trace (by simp) (fg_pow_three_of_fixed hK hσ htr)
  have hB12' : B ^ 12 = 1 := Subtype.ext (by simpa using hB12)
  rw [← QuotientGroup.mk_pow, hB12', QuotientGroup.mk_one]

end CFSG.OddStandard.SmallF3.Omega
