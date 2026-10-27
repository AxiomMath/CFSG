module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.Select
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.BorelForm

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open scoped MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SpecialLinear

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem exists_borel_conj (hm : 3 ≤ m)
    {ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) W}
    (hker : ∀ g, ρ g = 1 → g ∈ scalars m K)
    {A : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hint : ∀ a ∈ A, ∀ x, ∃ y, ∀ w, a (ρ x w) = ρ y (a w))
    (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (D : Subgroup (W ≃ₗ[ZMod 2] W)) (hDA : D ≤ A) :
    ∃ x : Matrix.SpecialLinearGroup (Fin m) K, ∀ d ∈ D,
      ∃ B : GL (Fin m) K, IsUpperGL B ∧ ∃ (τ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
        ∀ g w, d (ρ (x * g * x⁻¹) w) =
          ρ (x * borelStd m K B τ ε g * x⁻¹) (d w) := by
  classical
  have : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  have : CFSG.IsElementaryAbelian 2 ↥A := hAel
  have hD2 : IsPGroup 2 ↥D :=
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥A).to_le hDA
  have hDnorm : D ≤ rangeNormalizer (repUnits ρ) :=
    hDA.trans (le_rangeNormalizer_repUnits (ρ := ρ) (A := A) hint)
  obtain ⟨x, hx⟩ :=
    exists_conj_normalizes_unitriangular (π := repUnits ρ) hm D hDnorm hD2
  refine ⟨x, fun d hd => ?_⟩
  have haN : repUnits ρ x ∈ rangeNormalizer (repUnits ρ) :=
    (repUnits ρ).range.le_normalizer ⟨x, rfl⟩
  let e' : rangeNormalizer (repUnits ρ) :=
    ⟨(repUnits ρ x)⁻¹ * d * repUnits ρ x,
      mul_mem (mul_mem (Subgroup.inv_mem _ haN) (hDnorm hd)) haN⟩
  have he' : (e' : W ≃ₗ[ZMod 2] W) ∈
      Subgroup.normalizer ((unitriangular m K).map (repUnits ρ) :
        Set (W ≃ₗ[ZMod 2] W)) :=
    hx d hd
  obtain ⟨B, hB, τ, ε, hε, hlift⟩ :=
    liftAut_eq_borelStd_of_normalizes (π := repUnits ρ)
      (repUnits_ker_le_scalars (ρ := ρ) hker) hm e' he'
  refine ⟨B, hB, τ, ε, hε, fun g w => ?_⟩
  have hspec := liftAut_spec (π := repUnits ρ)
    (repUnits_ker_le_scalars (ρ := ρ) hker) hm e' g
  rw [hlift] at hspec
  have key : repUnits ρ x * repUnits ρ (borelStd m K B τ ε g) * (repUnits ρ x)⁻¹ =
      (d : W ≃ₗ[ZMod 2] W) * (repUnits ρ x * repUnits ρ g * (repUnits ρ x)⁻¹) *
        (d : W ≃ₗ[ZMod 2] W)⁻¹ := by
    rw [hspec]
    dsimp only [e']
    group
  have key' : repUnits ρ (x * borelStd m K B τ ε g * x⁻¹) =
      (d : W ≃ₗ[ZMod 2] W) * repUnits ρ (x * g * x⁻¹) *
        (d : W ≃ₗ[ZMod 2] W)⁻¹ := by
    simpa [map_mul, map_inv] using key
  have hval := congrArg
    (fun e : W ≃ₗ[ZMod 2] W => e ((d : W ≃ₗ[ZMod 2] W) w)) key'.symm
  have hinv : ∀ v : W, (repUnits ρ x).symm v = ρ x⁻¹ v := by
    intro v
    change ((repUnits ρ x)⁻¹ : W ≃ₗ[ZMod 2] W) v = ρ x⁻¹ v
    rw [← map_inv]
    exact repUnits_apply ρ x⁻¹ v
  simpa [repUnits_apply, hinv] using hval

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
