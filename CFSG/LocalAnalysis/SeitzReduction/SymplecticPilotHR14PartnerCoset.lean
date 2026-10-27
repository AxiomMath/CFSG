module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LULinear
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem congr_conj_eq_conj_apply (φ : X ≃* Y) (y : X) :
    MulAut.congr φ (MulAut.conj y) = MulAut.conj (φ y) := by
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem cosetInnConjInput_of_congr (φ : X ≃* Y) {θ : MulAut X}
    (h : CosetInnConjInput (MulAut.congr φ θ)) : CosetInnConjInput θ := by
  intro y hy2 ⟨β, hβ⟩
  have e1 : MulAut.conj (φ y) * MulAut.congr φ θ = MulAut.congr φ (MulAut.conj y * θ) := by
    rw [map_mul, congr_conj_eq_conj_apply]
  obtain ⟨z, hz⟩ := h (φ y) (by rw [e1, ← map_mul, hy2, map_one])
    ⟨MulAut.congr φ β, by rw [e1, ← map_mul, ← map_mul, hβ]⟩
  refine ⟨φ.symm z, (MulAut.congr φ).injective ?_⟩
  rw [← e1, hz, map_mul, map_mul, map_inv, congr_conj_eq_conj_apply, MulEquiv.apply_symm_apply]

theorem cosetInnConjInput_congr (φ : X ≃* Y) {θ : MulAut X} (h : CosetInnConjInput θ) :
    CosetInnConjInput (MulAut.congr φ θ) := by
  refine cosetInnConjInput_of_congr φ.symm ?_
  have : MulAut.congr φ.symm (MulAut.congr φ θ) = θ := by
    ext x
    simp [MulAut.congr_apply]
  rw [this]
  exact h

end Transport

section Model

variable {F : Type} [Field F] [Finite F]

theorem cosetInnConjInput_blockSwapJ [CharP F 2] {f m r : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) (hm : 3 ≤ m) (hr : m = 2 * r) {C : GL (Fin m) F}
    (hC : (C : Matrix (Fin m) (Fin m) F) = UnitaryHigher.blockSwapJ m r) {n' f' : ℕ}
    (hfix : LieModel (fixedSubgroup (conjAut m F C * dualAut m F)) .PSp n' 2 f') :
    CosetInnConjInput (conjAut m F C * dualAut m F) := by
  intro y hy2 ⟨β, hβ⟩
  obtain ⟨g, rfl⟩ := proj_surjective m F y
  set A : GL (Fin m) F := SpecialLinearGroup.toGL g * C with hA
  have hyA : MulAut.conj (proj m F g) * (conjAut m F C * dualAut m F) =
      conjAut m F A * dualAut m F := by
    rw [← conjAut_toGL, hA, map_mul, mul_assoc]
  rw [hyA] at hy2 hβ ⊢
  obtain ⟨-, ⟨H, C', hAm, hconj, hC'⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hF hm A (by rw [sq]; exact hy2)
  rcases hC' with ⟨hC'1, -⟩ | ⟨r', hr', hC'J, -⟩
  · exfalso
    have h1 : conjAut m F A * dualAut m F = MulAut.congr β (conjAut m F C * dualAut m F) := by
      rw [LinearPilot.mulAut_congr_eq_mul, hβ]
      group
    have h2 : conjAut m F A * dualAut m F =
        MulAut.congr (conjAut m F H) (conjAut m F C' * dualAut m F) := by
      rw [LinearPilot.mulAut_congr_eq_mul, hconj]
    have hfixA : LieModel (fixedSubgroup (conjAut m F A * dualAut m F)) .PSp n' 2 f' := by
      rw [h1]
      exact LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv β _) hfix
    rw [h2] at hfixA
    have hfixC' : LieModel (fixedSubgroup (conjAut m F C' * dualAut m F)) .PSp n' 2 f' :=
      LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv (conjAut m F H) _).symm
        hfixA
    exact not_lieModel_PSp_fixedSubgroup_dualAut_one hf hF hm ⟨r, by omega⟩ hC'1 hfixC'
  · obtain rfl : r' = r := by omega
    have hCC' : C' = C := Units.ext (hC'J.trans hC.symm)
    subst hCC'
    have hdet : (H : Matrix (Fin m) (Fin m) F).det = 1 := by
      have h1 := congrArg Matrix.det hAm
      rw [hA, Units.val_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, g.2,
        one_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
      have hC0 : (C' : Matrix (Fin m) (Fin m) F).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).1 C'.isUnit).ne_zero
      have h2 : (H : Matrix (Fin m) (Fin m) F).det * (H : Matrix (Fin m) (Fin m) F).det = 1 := by
        apply mul_right_cancel₀ hC0
        rw [one_mul]
        calc (H : Matrix (Fin m) (Fin m) F).det * (H : Matrix (Fin m) (Fin m) F).det *
              (C' : Matrix (Fin m) (Fin m) F).det =
            (H : Matrix (Fin m) (Fin m) F).det * (C' : Matrix (Fin m) (Fin m) F).det *
              (H : Matrix (Fin m) (Fin m) F).det := by ring
          _ = (C' : Matrix (Fin m) (Fin m) F).det := h1.symm
      exact eq_one_of_mul_self_eq_one_of_charTwo h2
    set Hs : SpecialLinearGroup (Fin m) F := ⟨H, hdet⟩ with hHs
    have hHs' : SpecialLinearGroup.toGL Hs = H := Units.ext rfl
    refine ⟨proj m F Hs, ?_⟩
    rw [← conjAut_toGL, hHs', hconj]

end Model

end CFSG.SeitzReduction.SymplecticPilot
