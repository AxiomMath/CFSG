module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4
import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.RankThree.PartOne.KCLinComm
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem aut_fix_blocks_sq [Finite F] (h2 : (2 : F) ≠ 0) (α : MulAut (projectiveSL 4 F))
    (hfix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range, α (proj 4 F r) = proj 4 F r)
    (hfix' : ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range, α (proj 4 F r) = proj 4 F r)
    (hα : α * α = MulAut.conj (proj 4 F (rootInv F (show 2 ≤ 4 by norm_num)))) :
    IsSquare (-1 : F) := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform α
  have hrootcongr : MulAut.conj (proj 4 F (rootInv F (show 2 ≤ 4 by norm_num))) =
      conjAut 4 F (Matrix.SpecialLinearGroup.toGL (rootInv F (show 2 ≤ 4 by norm_num))) :=
    (conjAut_toGL _).symm
  interval_cases ε
  · rw [pow_zero, mul_one] at hαeq
    subst hαeq
    obtain ⟨hσ, a, b, ha, hb, hM⟩ := aut_fix_blocks_zero h2 A σ hfix hfix'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one, hrootcongr, ← map_mul] at hα
    set X : GL (Fin 4) F := Matrix.SpecialLinearGroup.toGL (rootInv F (show 2 ≤ 4 by norm_num))
      with hX
    have h3 : conjAut 4 F (A * A * X⁻¹) = 1 := by rw [map_mul, hα, map_inv]; group
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff (by norm_num) _).mp h3
    have h4 : (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) =
        (c : F) • (X : Matrix (Fin 4) (Fin 4) F) := by
      have h5 : A * A = Matrix.GeneralLinearGroup.scalar (Fin 4) c * X := by
        rw [hc]; group
      have h6 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) h5
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul] at h6
      exact h6
    rw [hX, coe_toGL_rootInv, hM] at h4
    have e1 := congrFun (congrFun h4 0) 0
    have e2 := congrFun (congrFun h4 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_four] at e1 e2
    refine ⟨a * b⁻¹, ?_⟩
    have : a * a = -(b * b) := by linear_combination e1 + e2
    field_simp
    linear_combination -this
  · exfalso
    rw [pow_one] at hαeq
    subst hαeq
    obtain ⟨hσ, m, n, hm, hn, hM⟩ := aut_fix_blocks_one h2 A σ hfix hfix'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one, sq_of_antidiag A m n hm hn hM, hrootcongr] at hα
    have h3 : conjAut 4 F (Matrix.SpecialLinearGroup.toGL
        (rootInv F (show 2 ≤ 4 by norm_num))) = 1 := hα.symm
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff (by norm_num) _).mp h3
    have h6 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      coe_toGL_rootInv] at h6
    have e1 : (c : F) = -1 := by simpa using congrFun (congrFun h6 0) 0
    have e2 : (c : F) = 1 := by simpa using congrFun (congrFun h6 2) 2
    apply h2
    linear_combination e1 - e2

theorem psl4_autSq [Finite F] (h2 : (2 : F) ≠ 0) {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R') {x x' : SL(4, F)}
    (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1)
    (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F)) (φ : MulAut (projectiveSL 4 F))
    (hφ : ∀ r ∈ R, φ (proj 4 F r) = proj 4 F r) (hφ' : ∀ r ∈ R', φ (proj 4 F r) = proj 4 F r)
    (hφ2 : φ * φ = MulAut.conj (proj 4 F x)) : IsSquare (-1 : F) := by
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std h2 hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  set c : MulAut (projectiveSL 4 F) := MulAut.conj (proj 4 F g) with hcdef
  have hcp : ∀ s : SL(4, F), c (proj 4 F s) = proj 4 F (g * s * g⁻¹) := fun s => by
    rw [hcdef, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set α : MulAut (projectiveSL 4 F) := c⁻¹ * φ * c with hα
  have hαp : ∀ s : SL(4, F), α (proj 4 F s) = (c⁻¹) (φ (c (proj 4 F s))) := fun s => rfl
  have hfixα : ∀ (S : Subgroup SL(4, F)), (∀ r ∈ S.map (MulAut.conj g).toMonoidHom,
      φ (proj 4 F r) = proj 4 F r) → ∀ r ∈ S, α (proj 4 F r) = proj 4 F r := by
    intro S hS r hr
    have hmem : g * r * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨r, hr, rfl⟩
    rw [hαp, hcp, hS _ hmem, ← hcp]
    simp
  have hfix0 := hfixα (blockSL F 4 2 0 (by norm_num)).range (hRg ▸ hφ)
  have hfix2 := hfixα (blockSL F 4 2 2 (by norm_num)).range (hR'g ▸ hφ')
  have hconj : MulAut.conj (proj 4 F (g * rootInv F (show 2 ≤ 4 by norm_num) * g⁻¹)) =
      c * MulAut.conj (proj 4 F (rootInv F (show 2 ≤ 4 by norm_num))) * c⁻¹ := by
    rw [hcdef]
    simp only [map_mul, map_inv]
  have hα2 : α * α = MulAut.conj (proj 4 F (rootInv F (show 2 ≤ 4 by norm_num))) := by
    have h1 : α * α = c⁻¹ * (φ * φ) * c := by rw [hα]; group
    rw [h1, hφ2, hxg, hconj]
    group
  exact aut_fix_blocks_sq h2 α hfix0 hfix2 hα2

end CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
