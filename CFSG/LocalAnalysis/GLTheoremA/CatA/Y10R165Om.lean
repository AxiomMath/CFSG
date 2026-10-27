module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Concl
public import CFSG.RankThree.PartOne.KC.OrthogonalRegularQuasisimple
public import CFSG.RankThree.PartOne.S11d.OrthCaseH
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcE
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.Quasithin.Background.F918D5

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks QuadraticMap
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

namespace OmEngine

theorem polarBilin_isAlt (h2 : (2 : F) = 0) (Q : QuadraticForm F V) :
    LinearMap.BilinForm.IsAlt (polarBilin Q) := by
  intro v
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul,
    Nat.cast_ofNat, h2, zero_mul]

section Blocks

variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ} {Q : QuadraticForm F V}

theorem blockSpace_polar_nondegenerate [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A)
    (hB : ∀ a : ↥A, ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (D : Hyperplane A p) :
    (LinearMap.BilinForm.restrict (polarBilin Q) (blockSpace A D.1)).Nondegenerate := by
  have key : ∀ v ∈ blockSpace A D.1,
      (∀ w ∈ blockSpace A D.1, polarBilin Q v w = 0) → v = 0 := by
    intro v hv hvw
    refine hQ.1 v fun u => ?_
    obtain ⟨u₁, u₂, rfl⟩ :=
      exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) u
    rw [map_add, hvw (u₁ : V) u₁.2,
      blockSpace_ker_orthogonal A hp hpF hA (polarBilin Q) hB D hv u₂.2, add_zero]
  constructor
  · intro v hv
    refine Subtype.ext (key (v : V) v.2 fun w hw => ?_)
    have h := hv ⟨w, hw⟩
    rwa [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h
  · intro v hv
    refine Subtype.ext (key (v : V) v.2 fun w hw => ?_)
    have h := hv ⟨w, hw⟩
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h
    rw [polarBilin_apply_apply, QuadraticMap.polar_comm, ← polarBilin_apply_apply]
    exact h

theorem even_finrank_blockSpace [FiniteDimensional F V] (h2 : (2 : F) = 0)
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A)
    (hB : ∀ a : ↥A, ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (D : Hyperplane A p) : Even (Module.finrank F ↥(blockSpace A D.1)) := by
  have halt : (LinearMap.BilinForm.restrict (polarBilin Q) (blockSpace A D.1)).IsAlt := by
    intro w
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat, h2, zero_mul]
  exact LinearMap.BilinForm.IsAlt.even_finrank halt
    (blockSpace_polar_nondegenerate A hQ hp hpF hA hB D)

theorem two_le_finrank_blockSpace [FiniteDimensional F V] (h2 : (2 : F) = 0)
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A)
    (hB : ∀ a : ↥A, ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (D : Hyperplane A p) (hD : blockSpace A D.1 ≠ ⊥) :
    2 ≤ Module.finrank F ↥(blockSpace A D.1) := by
  have hev := even_finrank_blockSpace A h2 hQ hp hpF hA hB D
  have hpos : 0 < Module.finrank F ↥(blockSpace A D.1) := by
    rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
    exact hD
  obtain ⟨k, hk⟩ := hev
  omega

theorem finrank_eq_finrank_fixedSpaceOf_add_sum_blockSpace [FiniteDimensional F V]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) :
    Module.finrank F V = Module.finrank F ↥(fixedSpaceOf A) +
      ∑ D : Hyperplane A p, Module.finrank F ↥(blockSpace A D.1) := by
  classical
  have hcompl : IsCompl (fixedSpaceOf A) (commutatorSpaceOf A) :=
    isCompl_fixedSpaceOf_commutatorSpaceOf A hp hpF hA
  have h₁ : Module.finrank F V = Module.finrank F ↥(fixedSpaceOf A) +
      Module.finrank F ↥(commutatorSpaceOf A) :=
    (Submodule.finrank_add_eq_of_isCompl hcompl).symm
  have hInt : DirectSum.IsInternal (blockSpaceU A hp hpF hA) := isInternal_blockSpaceU A hp hpF hA
  have h₂ : Module.finrank F ↥(commutatorSpaceOf A) =
      ∑ D : Hyperplane A p, Module.finrank F ↥(blockSpace A D.1) := by
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap (blockSpaceU A hp hpF hA))
      hInt).finrank_eq, Module.finrank_directSum]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [blockSpace_eq_map_blockSpaceU A hp hpF hA D, Submodule.finrank_map_subtype_eq]
  rw [h₁, h₂]

theorem sum_finrank_blockSpace_le_finrank [FiniteDimensional F V]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) :
    ∑ D : Hyperplane A p, Module.finrank F ↥(blockSpace A D.1) ≤ Module.finrank F V := by
  have h := finrank_eq_finrank_fixedSpaceOf_add_sum_blockSpace A hp hpF hA
  omega

end Blocks

end OmEngine

namespace OmEngine

section Fixed

variable [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {x : V ≃ₗ[F] V}

theorem even_finrank_fixedSpace (hx : OddOrderIsometry Q p x)
    (h2 : (2 : F) = 0) : Even (Module.finrank F ↥(fixedSpace x)) :=
  LinearMap.BilinForm.IsAlt.even_finrank
    (polarBilin_isAlt h2 (Q.comp (fixedSpace x).subtype))
    hx.polarBilin_fixed_nondegenerate

theorem isQuasisimple_supportedFixedDerived_of_six_le [Finite F]
    {Q : QuadraticForm F V} {p : ℕ} {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x)
    (h2 : (2 : F) = 0) (h6 : 6 ≤ Module.finrank F ↥(fixedSpace x)) :
    CFSG.IsQuasisimple ↥(supportedFixedDerived Q x) := by
  have h3 : 3 ≤ Module.finrank F ↥(fixedSpace x) := by omega
  have hnexc : ¬ SmallFixedException (Q.comp (fixedSpace x).subtype) := by
    rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> omega
  have hns : ¬ (Module.finrank F ↥(fixedSpace x) = 4 ∧
      ∃ S : Submodule F ↥(fixedSpace x), Module.finrank F S = 2 ∧
        ∀ y ∈ S, (Q.comp (fixedSpace x).subtype) y = 0) := by
    rintro ⟨h, -⟩
    omega
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (supportedFixedDerivedEquiv hx).symm
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (CFSG.RankThree.PartOne.orthDerivedEquivCommutator _)
      (orthogonal_regular_space_derived_quasisimple _
        hx.polarBilin_fixed_nondegenerate h3 hnexc hns))

end Fixed

end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
