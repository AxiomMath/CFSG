module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldDef
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldSemi

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.LieType.Chevalley (fixSubfield mem_fixSubfield)

variable {p f : ℕ} {F : Type} [Field F]

theorem closure_fixed_eq_top_unitary_semi [Finite F] (h : UnitaryFieldData p f F)
    (T : FrobData F) (hgen : SubfieldDiagGen h (fixSubfield T.τ)) {y P : unitaryIsom3 h}
    {u : Fin 3 → F}
    (hP : ∀ i j, T.τ (((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) =
      ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j)
    (hPu : (((P : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal u) :
    Subgroup.closure {x : unitarySU p f F 3 | suField h T.τ x = x ∨ suConj h y x = x} = ⊤ := by
  have hPfix : glAut T.τ (P : GL (Fin 3) F) = P := by
    apply Units.ext
    rw [coe_glAut]
    ext i j
    exact hP i j
  have hPinv : glAut T.τ (P : GL (Fin 3) F)⁻¹ = (P : GL (Fin 3) F)⁻¹ := by
    rw [map_inv, hPfix]
  set H := Subgroup.closure {x : unitarySU p f F 3 | suField h T.τ x = x ∨ suConj h y x = x}
    with hH
  have hHtop : H.comap (suConj h P).toMonoidHom = ⊤ := by
    apply hgen
    · intro g hg
      have hgfix : glAut T.τ (g : GL (Fin 3) F) = g := by
        apply Units.ext
        rw [coe_glAut]
        ext i j
        exact (mem_fixSubfield T.τ).1 (hg i j)
      apply Subgroup.subset_closure
      left
      apply Subtype.ext
      rw [coe_suField]
      change glAut T.τ ((P : GL (Fin 3) F) * (g : GL (Fin 3) F) * (P : GL (Fin 3) F)⁻¹) =
        (P : GL (Fin 3) F) * (g : GL (Fin 3) F) * (P : GL (Fin 3) F)⁻¹
      rw [map_mul, map_mul, hPfix, hgfix, hPinv]
    · intro g hg
      apply Subgroup.subset_closure
      right
      apply Subtype.ext
      have hgd : (g : GL (Fin 3) F).val = Matrix.diagonal (fun i => (g : GL (Fin 3) F).val i i) :=
        (Matrix.IsDiag.diagonal_diag hg).symm
      have hPQ : ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (((P : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
        Units.mul_inv _
      have hQP : (((P : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := Units.inv_mul _
      have hcomm := commute_conj_of_commute_aux hPQ hQP hPu
        (T := (g : GL (Fin 3) F).val) (by
          rw [hgd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
          congr 1
          ext i
          exact mul_comm _ _)
      change (y : GL (Fin 3) F) * ((P : GL (Fin 3) F) * (g : GL (Fin 3) F) *
        (P : GL (Fin 3) F)⁻¹) * (y : GL (Fin 3) F)⁻¹ = (P : GL (Fin 3) F) * (g : GL (Fin 3) F) *
          (P : GL (Fin 3) F)⁻¹
      rw [mul_inv_eq_iff_eq_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul]
      simpa [Matrix.mul_assoc] using hcomm
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := (suConj h P).surjective x
  have : g ∈ H.comap (suConj h P).toMonoidHom := by rw [hHtop]; trivial
  exact this

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
