module

public import CFSG.Adapters.TauCetiExceptional.BigCellNormal
public import CFSG.Adapters.TauCetiExceptional.FrameworkClosure

public noncomputable section

namespace CFSG.TauCetiBridge

open CFSG.Blueprint.Chevalley TauCeti BigCell MvPolynomial

@[expose] def GeckRootGenerated (t : DynkinType) (ht : t.Valid) : Prop :=
  t.geckDefiningIdeal ht = UniversalEnvelopingAlgebra.kostantGeneratedDefiningIdeal
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht) (t.geckCoordinateBasisFin ht)

namespace GeckMatch

variable {τ : Tag} {t : DynkinType} {ht : t.Valid} (M : GeckMatch τ t ht)

@[expose] def geckIdx (i : Fin (nLab τ)) : Fin (t.geckDim ht) :=
  M.lab.symm ((posEquiv τ).symm i)

theorem lab_geckIdx
    (i : Fin (nLab τ)) : M.lab (M.geckIdx i) = (posEquiv τ).symm i :=
  M.lab.apply_symm_apply _

@[expose] def geckSubst (ij : Fin (nLab τ) × Fin (nLab τ)) :
    MvPolynomial (Fin (t.geckDim ht) × Fin (t.geckDim ht)) ℤ :=
  C ((M.sgn (M.geckIdx ij.1) : ℤ) * (M.sgn (M.geckIdx ij.2) : ℤ)) *
    X (M.geckIdx ij.1, M.geckIdx ij.2)

theorem sgn_mul_sgn {A : Type} [CommRing A] (s : ℤˣ) : ((s : ℤ) : A) * ((s : ℤ) : A) = 1 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp

theorem natMat_toGeck_symm_apply (A : Type) [CommRing A]
    (z : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) (i j : Fin (nLab τ)) :
    natMat τ A ((M.toGeck A).symm z : Module.End A (RootModule τ A)) i j =
      ((M.sgn (M.geckIdx i) : ℤ) : A) *
        (z : Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) (M.geckIdx i) (M.geckIdx j) *
          ((M.sgn (M.geckIdx j) : ℤ) : A) := by
  have h := M.toGeck_apply A ((M.toGeck A).symm z) (M.geckIdx i) (M.geckIdx j)
  rw [MulEquiv.apply_symm_apply, M.lab_geckIdx, M.lab_geckIdx] at h
  rw [natMat_apply, h]
  rw [show ∀ a b c : A, a * (a * b * c) * c = (a * a) * b * (c * c) from fun a b c => by ring,
    sgn_mul_sgn, sgn_mul_sgn, one_mul, mul_one]

theorem evalMat_natMat_toGeck_symm (A : Type) [CommRing A]
    (z : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A)
    (P : MvPolynomial (Fin (nLab τ) × Fin (nLab τ)) ℤ) :
    evalMat (natMat τ A ((M.toGeck A).symm z : Module.End A (RootModule τ A))) P =
      aeval (fun ij : Fin (t.geckDim ht) × Fin (t.geckDim ht) =>
        (z : Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) ij.1 ij.2)
        (bind₁ M.geckSubst P) := by
  rw [aeval_bind₁, aeval_eq_eval₂Hom, algebraMap_int_eq, evalMat]
  congr 2
  funext ij
  rw [natMat_toGeck_symm_apply, geckSubst, map_mul, aeval_C, aeval_X, algebraMap_int_eq,
    eq_intCast, Int.cast_mul]
  ring

@[expose] def nativeCarrier (L : Type) [Field L] : Subgroup (ModGL τ L) :=
  (t.geckPoints ht L).map (M.toGeck L).symm.toMonoidHom

theorem toGeck_mem_geckPoints_of_mem_nativeCarrier {L : Type} [Field L] {h : ModGL τ L}
    (hh : h ∈ M.nativeCarrier L) : M.toGeck L h ∈ t.geckPoints ht L := by
  obtain ⟨z, hz, rfl⟩ := hh
  change M.toGeck L ((M.toGeck L).symm z) ∈ _
  rwa [MulEquiv.apply_symm_apply]

theorem adjointGroup_le_nativeCarrier
    (L : Type) [Field L] :
    adjointGroup τ L ≤ M.nativeCarrier L := fun g hg =>
  ⟨M.toGeck L g, M.map_toGeck_adjointGroup_le_geckPoints L ⟨g, hg, rfl⟩,
    (M.toGeck L).symm_apply_apply g⟩

theorem vanishes_of_mem_nativeCarrier
    (hgen : GeckRootGenerated t ht) (L : Type) [Field L]
    {h : ModGL τ L} (hh : h ∈ M.nativeCarrier L) (P : MvPolynomial (Fin (nLab τ) × Fin (nLab τ)) ℤ)
    (hP : VanishesOnRat τ P) :
    evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0 := by
  have e := M.evalMat_natMat_toGeck_symm L (M.toGeck L h) P
  rw [MulEquiv.symm_apply_apply] at e
  rw [e]
  refine M.aeval_eq_zero_of_forall_adjointGroup hgen _ (fun g hg => ?_) L _
    (M.toGeck_mem_geckPoints_of_mem_nativeCarrier hh)
  have e' := M.evalMat_natMat_toGeck_symm ℚ (M.toGeck ℚ g) P
  rw [MulEquiv.symm_apply_apply] at e'
  rw [← e']
  exact hP g hg

theorem mem_adjointGroup_of_mem_nativeCarrier
    (hgen : GeckRootGenerated t ht) {L : Type}
    [Field L] [IsAlgClosed L] {h : ModGL τ L} (hh : h ∈ M.nativeCarrier L)
    (hΔ : bigCellDet (natMat τ L (h : Module.End L (RootModule τ L))) ≠ 0) :
    h ∈ adjointGroup τ L :=
  mem_adjointGroup_of_isUnit_bigCellDet h (M.vanishes_of_mem_nativeCarrier hgen L hh) hΔ

theorem nativeCarrier_le_normalizer
    (hgen : GeckRootGenerated t ht) (L : Type) [Field L]
    [IsAlgClosed L] :
    M.nativeCarrier L ≤ Subgroup.normalizer (adjointGroup τ L : Set (ModGL τ L)) :=
  le_normalizer_adjointGroup _ (M.adjointGroup_le_nativeCarrier L)
    fun _ hh => M.vanishes_of_mem_nativeCarrier hgen L hh

end GeckMatch

end CFSG.TauCetiBridge
