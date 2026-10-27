module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLModels
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeData
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Arf
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.RankThree.PartTwo CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
  CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem stated_model_of_isometry {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm (ZMod 2) W}
    {Q₀ : (ι → ZMod 2) → ZMod 2} (φ : W ≃ₗ[ZMod 2] (ι → ZMod 2)) (hφ : ∀ v, Q₀ (φ v) = Q v)
    {T : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)} (hT : T = ⁅orthGL Q, orthGL Q⁆) :
    (∀ g ∈ T, ∃ A ∈ StatedOmega Q₀,
      ∀ w : W, (A : Matrix ι ι (ZMod 2)) *ᵥ φ w = φ ((g : W →ₗ[ZMod 2] W) w)) ∧
    ∀ A ∈ StatedOmega Q₀, ∃ g ∈ T,
      ∀ w : W, (A : Matrix ι ι (ZMod 2)) *ᵥ φ w = φ ((g : W →ₗ[ZMod 2] W) w) := by
  set e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W with he
  have hmap : T.map e.toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [hT, Subgroup.map_commutator]
    unfold orthGL
    rw [Subgroup.map_comap_eq_self_of_surjective e.surjective]
  have hS := statedOmega_map_toLinEquiv_eq φ hφ
  have key : ∀ (A : GL ι (ZMod 2)) (g : LinearMap.GeneralLinearGroup (ZMod 2) W),
      toLinEquiv ι (ZMod 2) A = conjAut φ (e g) →
      ∀ w : W, (A : Matrix ι ι (ZMod 2)) *ᵥ φ w = φ ((g : W →ₗ[ZMod 2] W) w) := by
    intro A g hAg w
    have := congrArg (fun f : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) => f (φ w)) hAg
    simpa [conjAut_apply, e, he] using this
  constructor
  · intro g hg
    have h1 : e g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ := hmap ▸ ⟨g, hg, rfl⟩
    have : conjAut φ (e g) ∈ (StatedOmega Q₀).map (toLinEquiv ι (ZMod 2)).toMonoidHom := by
      rw [hS]
      exact ⟨e g, h1, rfl⟩
    obtain ⟨A, hA, hAe⟩ := this
    exact ⟨A, hA, key A g hAe⟩
  · intro A hA
    have : toLinEquiv ι (ZMod 2) A ∈ (StatedOmega Q₀).map (toLinEquiv ι (ZMod 2)).toMonoidHom :=
      ⟨A, hA, rfl⟩
    rw [hS] at this
    obtain ⟨h, hh, hhA⟩ := this
    rw [← hmap] at hh
    obtain ⟨g, hg, rfl⟩ := hh
    exact ⟨g, hg, key A g hhA.symm⟩

theorem isOmegaModel_of_orth {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (Q : QuadraticForm (ZMod 2) W)
    (hQ : (_root_.QuadraticMap.polarBilin Q).Nondegenerate)
    {T : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)} (hT : T = ⁅orthGL Q, orthGL Q⁆) :
    (∃ m, IsOmegaPlusModel T m) ∨ ∃ m, IsOmegaMinusModel T m := by
  obtain ⟨ε, m, hstd, hm⟩ := exists_isStdSpace Q (hQ : PolarNondeg Q)
  cases ε
  · right
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := hm rfl; omega⟩
    obtain ⟨φ, hφ⟩ := (hstd : IsMinusSpace Q (k + 1))
    have hφ' : ∀ v, StatedQuadMinus (k + 1) (ZMod 2) 1 1 (φ v) = Q v := fun v => by
      rw [← CFSG.LieType.Universal.Spin.coe_quadMinus]; exact hφ v
    exact ⟨k, φ, stated_model_of_isometry φ hφ' hT⟩
  · left
    obtain ⟨φ, hφ⟩ := (hstd : IsPlusSpace Q m)
    have hφ' : ∀ v, StatedQuadPlus m (ZMod 2) (φ v) = Q v := fun v => by
      rw [← CFSG.LieType.Universal.Spin.coe_quadPlus]; exact hφ v
    exact ⟨m, φ, stated_model_of_isometry φ hφ' hT⟩

end CFSG.HardMathSupport.Cooperstein.StructureLie
