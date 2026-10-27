module

public import CFSG.Adapters.TauCetiExceptional.BigCellBruhat
public import CFSG.LieType.Chevalley.LangAdjointDiagonalLift
public import CFSG.Adapters.TauCetiExceptional.BigCellCore
public import CFSG.Adapters.TauCetiExceptional.BigCellGeneric

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag}

@[expose] def VanishesOnRat
    (τ : Tag) (P : MvPolynomial (Fin (nLab τ) × Fin (nLab τ)) ℤ) :
    Prop :=
  ∀ g ∈ adjointGroup τ ℚ, evalMat (natMat τ ℚ (g : Module.End ℚ (RootModule τ ℚ))) P = 0

theorem exists_ringHom_mapMatrix_genMat
    {A : Type} [CommRing A]
    (M : Matrix (Fin (nLab τ)) (Fin (nLab τ)) A)
    (hM : ∀ P, VanishesOnRat τ P → evalMat M P = 0) (hMunit : IsUnit (bigCellDet M)) :
    ∃ ψ : GenRing τ →+* A, ψ.mapMatrix (genMat τ) = M := by
  refine exists_ringHom_mapMatrix_eq (genMat τ) (isUnit_bigCellDet_genMat τ)
    (fun T hT hinv => eq_top_of_genMat T hT hinv)
    ((fun g : ModGL τ ℚ => natMat τ ℚ (g : Module.End ℚ (RootModule τ ℚ))) ''
      (adjointGroup τ ℚ : Set (ModGL τ ℚ))) ?_ M ?_ hMunit
  · rintro _ ⟨g, hg, rfl⟩ hΔ
    obtain ⟨cm, a, cp, h⟩ := exists_bigCellMat_eq_natMat hg hΔ
    exact ⟨specialize cm a cp, (mapMatrix_specialize_genMat cm a cp).trans h⟩
  · intro P hP
    exact hM P fun g hg => hP _ ⟨g, hg, rfl⟩

theorem mem_adjointGroup_of_isUnit_bigCellDet
    {L : Type} [Field L] [IsAlgClosed L]
    (z : ModGL τ L) (hz : ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (z : Module.End L (RootModule τ L))) P = 0)
    (hΔ : bigCellDet (natMat τ L (z : Module.End L (RootModule τ L))) ≠ 0) :
    z ∈ adjointGroup τ L := by
  obtain ⟨ψ, hψ⟩ := exists_ringHom_mapMatrix_genMat _ hz (isUnit_iff_ne_zero.2 hΔ)
  rw [genMat, mapMatrix_bigCellMat, bigCellMat_eq_natMat] at hψ
  have hz' := Units.ext ((natMat τ L).injective hψ)
  rw [← hz']
  have hBC := ((triangular_borel_structure.{0, 0} τ L).2.2.2.2.2.2.2.2.2.2.2 L).1
  have hU : ∀ c, uProd L c ∈ adjointGroup τ L := fun c =>
    hBC (Subgroup.mem_sup_right (uProd_mem_posUnipotent c))
  have hn : nLong L ∈ adjointGroup τ L := canonicalRep_mem_adjointGroup _ L _
  exact mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hn) (hU _)) hn)
    (exceptional_Lang_adjoint_diagonal_lift τ L _).1) (hU _)

end CFSG.TauCetiBridge.BigCell
