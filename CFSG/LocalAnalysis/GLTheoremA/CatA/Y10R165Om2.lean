module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks QuadraticMap
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ} {Q : QuadraticForm F V}

namespace OmEngine

variable [FiniteDimensional F V]

theorem blockEnd_oddOrderIsometry (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (hQ : (polarBilin Q).Nondegenerate)
    (hQinv : ∀ a : ↥A, ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) :
    OddOrderIsometry Q p (blockEnd A hp hpF hA t ht D) where
  mem := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    exact blockEnd_quadratic A hp hpF hA Q hQinv t ht D
  pow_eq_one := blockEnd_pow A hp hpF hA t ht D
  cast_ne_zero := hpF
  regular := fun v hv => hQ.1 v fun w => by
    have h := hv w
    rw [polarBilin_apply_apply]
    exact h

theorem fixedByEnd_blockEnd_eq_ker_projBlock (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : Hyperplane A p) :
    fixedByEnd (blockEnd A hp hpF hA t ht D) = LinearMap.ker (projBlock A hp hpF hA D) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [mem_fixedByEnd] at hv
    obtain ⟨u, r, hcu, rfl⟩ :=
      exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
    have hr : ((r : V)) ∈ LinearMap.ker (projBlock A hp hpF hA D) := r.2
    have h1 : blockEnd A hp hpF hA t ht D ((u : V) + (r : V)) =
        (t D : V ≃ₗ[F] V) (u : V) + (r : V) := by
      rw [map_add, blockEnd_apply_mem A hp hpF hA t ht D u.2,
        blockEnd_apply_of_ker A hp hpF hA t ht D hr]
    rw [h1] at hv
    have h2 : (t D : V ≃ₗ[F] V) (u : V) = (u : V) := add_right_cancel hv
    have h3 : (u : V) = 0 := eq_zero_of_fixed_mem_blockSpace A hp hpF hA (ht D) u.2 h2
    rw [LinearMap.mem_ker, map_add, projBlock_apply_of_mem A hp hpF hA D u.2,
      LinearMap.mem_ker.mp hr, h3]
    simp
  · intro v hv
    rw [mem_fixedByEnd]
    exact blockEnd_apply_of_ker A hp hpF hA t ht D (by rw [LinearMap.mem_ker]; exact hv)

theorem fixedSpace_blockEnd_eq_ker_projBlock (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : Hyperplane A p) :
    CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (blockEnd A hp hpF hA t ht D) =
      LinearMap.ker (projBlock A hp hpF hA D) := by
  rw [← fixedByEnd_blockEnd_eq_ker_projBlock A hp hpF hA t ht D]
  ext v
  rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace, mem_fixedByEnd]

theorem finrank_fixedSpace_blockEnd (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : Hyperplane A p) :
    Module.finrank F ↥(CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
        (blockEnd A hp hpF hA t ht D)) =
      Module.finrank F V - Module.finrank F ↥(blockSpace A D.1) := by
  rw [fixedSpace_blockEnd_eq_ker_projBlock A hp hpF hA t ht D]
  have h := finrank_ker_projBlock_add_finrank_blockSpace A hp hpF hA D
  omega

theorem ker_inf_le_fixedSpace_blockEnd_mul (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D E : Hyperplane A p} :
    LinearMap.ker (projBlock A hp hpF hA D) ⊓ LinearMap.ker (projBlock A hp hpF hA E) ≤
      CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
        (blockEnd A hp hpF hA t ht D * blockEnd A hp hpF hA t ht E) := by
  intro v hv
  rw [Submodule.mem_inf] at hv
  rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace, LinearEquiv.mul_apply]
  have h1 : blockEnd A hp hpF hA t ht D v = v :=
    blockEnd_apply_of_ker A hp hpF hA t ht D (LinearMap.mem_ker.mpr hv.1)
  have h2 : blockEnd A hp hpF hA t ht E v = v :=
    blockEnd_apply_of_ker A hp hpF hA t ht E (LinearMap.mem_ker.mpr hv.2)
  rw [h2, h1]

theorem le_finrank_fixedSpace_blockEnd_mul (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D E : Hyperplane A p} :
    Module.finrank F V - Module.finrank F ↥(blockSpace A D.1) -
        Module.finrank F ↥(blockSpace A E.1) ≤
      Module.finrank F ↥(CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
        (blockEnd A hp hpF hA t ht D * blockEnd A hp hpF hA t ht E)) := by
  have hdimD := finrank_ker_projBlock_add_finrank_blockSpace A hp hpF hA D
  have hdimE := finrank_ker_projBlock_add_finrank_blockSpace A hp hpF hA E
  have hmono := Submodule.finrank_mono (ker_inf_le_fixedSpace_blockEnd_mul A hp hpF hA t ht
    (D := D) (E := E))
  have hsup : Module.finrank F ↥(LinearMap.ker (projBlock A hp hpF hA D) ⊔
      LinearMap.ker (projBlock A hp hpF hA E)) ≤ Module.finrank F V := by
    have h := Submodule.finrank_mono (le_top : LinearMap.ker (projBlock A hp hpF hA D) ⊔
      LinearMap.ker (projBlock A hp hpF hA E) ≤ (⊤ : Submodule F V))
    rwa [finrank_top] at h
  have hinf := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (projBlock A hp hpF hA D)) (LinearMap.ker (projBlock A hp hpF hA E))
  omega

end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
