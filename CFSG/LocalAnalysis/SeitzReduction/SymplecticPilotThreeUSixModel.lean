module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryTransport
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOmegaLevi
public import CFSG.RankThree.PartOne.CTP.Su4Std

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.RankThree.PartOne.CTP (lbEmb sbEmb matS embMid sbMat matS_lbElt matS_sbElt)
open scoped MatrixGroups

section Coords

theorem ctuGramIdx_two_apply (i : Fin 4) :
    (ctuGramIdx 2 i : Fin 4) = Equiv.swap (2 : Fin 4) 3 i := by
  obtain ⟨u, rfl⟩ := (spModelIdx 2).surjective i
  apply Fin.ext
  rw [ctuGramIdx_spModelIdx]
  rcases u with a | a
  · have hv := spModelIdx_inl_val (n := 2) a
    rw [ctuCoord_inl_inl]
    generalize spModelIdx 2 (Sum.inl a) = x at hv ⊢
    revert a x
    decide
  · have hv := spModelIdx_inr_val (n := 2) a
    rw [ctuCoord_inl_inr]
    generalize spModelIdx 2 (Sum.inr a) = x at hv ⊢
    revert a x
    decide

theorem unitaryInvolution_eq_bar {f : ℕ} {K' : Type} [Field K'] [Finite K'] [CharP K' 2]
    (h : UnitaryFieldData 2 f K') (c : K') : unitaryInvolution K' 2 f c = h.bar c := by
  rw [unitaryInvolution_apply, h.bar_apply]

end Coords

section Chi

variable {f : ℕ} {K' : Type} [Field K'] [Finite K'] [CharP K' 2] (h : UnitaryFieldData 2 f K')
  {C₀ : GL (Fin (2 * 2)) K'}
  (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)

theorem coe_ctuGramEquiv_refl_apply (y : SU (unitaryInvolution K' 2 f) (2 * 2 + 0))
    (i j : Fin 4) :
    (((ctuGramEquiv h hC₀ (RingEquiv.refl K') y : gramSU h
        (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) : GL (Fin (2 * 2)) K') :
          Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') i j =
      ((y : GL (Fin (2 * 2 + 0)) K') : Matrix (Fin (2 * 2 + 0)) (Fin (2 * 2 + 0)) K')
        (Equiv.swap (2 : Fin 4) 3 i) (Equiv.swap (2 : Fin 4) 3 j) := by
  rw [ctuGramEquiv_apply, coe_ctuGramHom, transportMat, Matrix.map_apply,
    Matrix.submatrix_apply, ctuGramIdx_two_apply, ctuGramIdx_two_apply]
  rfl

theorem ctuGramEquiv_sbEmb (N : SL(2, K')) :
    ctuGramEquiv h hC₀ (RingEquiv.refl K')
        (sbEmb (unitaryInvolution K' 2 f) (unitaryInvolution_involutive h.card_eq_sq) N) =
      lambdaU h hC₀ N := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [coe_ctuGramEquiv_refl_apply, coe_lambdaU, lambdaUMat_eq]
  change sbMat (unitaryInvolution K' 2 f) (N : Matrix (Fin 2) (Fin 2) K')
    (Equiv.swap (2 : Fin 4) 3 i) (Equiv.swap (2 : Fin 4) 3 j) = _
  fin_cases i <;> fin_cases j <;>
    simp [sbMat, Equiv.swap_apply_def, unitaryInvolution_eq_bar h]

theorem map_range_sbEmb_ctuGramEquiv :
    (sbEmb (unitaryInvolution K' 2 f) (unitaryInvolution_involutive h.card_eq_sq)).range.map
        (ctuGramEquiv h hC₀ (RingEquiv.refl K')).toMonoidHom =
      (lambdaU h hC₀).range := by
  rw [← MonoidHom.range_comp]
  congr 1
  exact MonoidHom.ext fun N => ctuGramEquiv_sbEmb h hC₀ N

theorem coe_ctuGramEquiv_lbEmb (N : SU (unitaryInvolution K' 2 f) 2) :
    (((ctuGramEquiv h hC₀ (RingEquiv.refl K') (lbEmb (unitaryInvolution K' 2 f) N) :
        gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) : GL (Fin (2 * 2)) K') :
          Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') =
      !![1, 0, 0, 0; 0, matS _ N 0 0, 0, matS _ N 0 1; 0, 0, 1, 0;
        0, matS _ N 1 0, 0, matS _ N 1 1] := by
  ext i j
  rw [coe_ctuGramEquiv_refl_apply]
  change embMid (matS (unitaryInvolution K' 2 f) N)
    (Equiv.swap (2 : Fin 4) 3 i) (Equiv.swap (2 : Fin 4) 3 j) = _
  fin_cases i <;> fin_cases j <;> simp [embMid, Equiv.swap_apply_def]

end Chi

end CFSG.SeitzReduction.SymplecticPilot
