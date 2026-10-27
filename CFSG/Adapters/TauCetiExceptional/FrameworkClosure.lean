module

public import CFSG.Adapters.TauCetiExceptional.FrameworkTransport
public import CFSG.Adapters.TauCetiExceptional.FrameworkHopf

public noncomputable section

open CFSG.Blueprint.Chevalley TauCeti WithConv

namespace CFSG.TauCetiBridge

theorem symmetricAlgebra_eq_zero_of_forall_rat (z : SymmetricAlgebra ℤ ℤ)
    (h : ∀ c : ℚ, ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := ℚ)).symm
      (Multiplicative.ofAdd c)).ofConv z = 0) : z = 0 := by
  let b := Module.Basis.singleton Unit ℤ
  let e := SymmetricAlgebra.equivMvPolynomial b
  have he1 : e (SymmetricAlgebra.ι ℤ ℤ 1) = MvPolynomial.X () := by
    simpa [b] using SymmetricAlgebra.equivMvPolynomial_ι_apply b ()
  have hpt : ∀ c : ℚ,
      (MvPolynomial.aeval (R := ℤ) fun _ : Unit => c).comp
          (e : SymmetricAlgebra ℤ ℤ →ₐ[ℤ] MvPolynomial Unit ℤ) =
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := ℚ)).symm
          (Multiplicative.ofAdd c)).ofConv := by
    intro c
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext_ring
    change MvPolynomial.aeval (R := ℤ) (fun _ : Unit => c) (e (SymmetricAlgebra.ι ℤ ℤ 1)) = _
    rw [he1, MvPolynomial.aeval_X, LinearMap.comp_apply]
    exact (AdditiveGroup.gaPointsMulEquiv_symm_apply_ι (Multiplicative.ofAdd c)).symm
  have hmap : MvPolynomial.map (algebraMap ℤ ℚ) (e z) = 0 := by
    apply MvPolynomial.funext
    intro x
    have hx := (DFunLike.congr_fun (hpt (x ())) z).trans (h (x ()))
    change MvPolynomial.aeval (R := ℤ) (fun _ : Unit => x ()) (e z) = 0 at hx
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map] at hx
    have hxx : (fun _ : Unit => x ()) = x := funext fun u => by cases u; rfl
    rw [hxx] at hx
    rw [hx, map_zero]
  have hez : e z = 0 :=
    MvPolynomial.map_injective _ (IsFractionRing.injective ℤ ℚ) (hmap.trans (map_zero _).symm)
  exact e.injective (hez.trans (map_zero e).symm)

namespace GeckMatch

variable {τ : Tag} {t : DynkinType} {ht : t.Valid} (M : GeckMatch τ t ht)

def ratNativePoints :
    Subgroup (WithConv (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht) →ₐ[ℤ] ℚ)) :=
  ((adjointGroup τ ℚ).map (M.toGeck ℚ).toMonoidHom).map
    (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) (t.geckDim ht)).symm.toMonoidHom

def nativeVanishingIdeal :
    HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) :=
  fracVanishingIdeal (R := ℤ) (K := ℚ) M.ratNativePoints

theorem pointsMulEquiv_symm_toGeck_mem (g : ModGL τ ℚ) (hg : g ∈ adjointGroup τ ℚ) :
    (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) (t.geckDim ht)).symm (M.toGeck ℚ g) ∈
      M.ratNativePoints :=
  ⟨M.toGeck ℚ g, ⟨g, hg, rfl⟩, rfl⟩

theorem nativeVanishingIdeal_le_geckDefiningIdeal
    (hgen : t.geckDefiningIdeal ht = UniversalEnvelopingAlgebra.kostantGeneratedDefiningIdeal
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht) (t.geckCoordinateBasisFin ht)) :
    M.nativeVanishingIdeal ≤ t.geckDefiningIdeal ht := by
  rw [hgen, UniversalEnvelopingAlgebra.le_kostantGeneratedDefiningIdeal_iff]
  intro j x hx
  rw [RingHom.mem_ker]
  apply symmetricAlgebra_eq_zero_of_forall_rat
  intro c
  obtain ⟨g, hg, hgeq⟩ : ∃ g ∈ adjointGroup τ ℚ, M.toGeck ℚ g =
      (t.geckRootSubgroupPoints ht j ℚ (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) ℚ) := by
    rcases j with i | i
    · exact ⟨xUnit τ ℚ (M.node i) c, xUnit_mem_adjointGroup _ _, M.toGeck_xUnit ℚ i c⟩
    · exact ⟨yUnit τ ℚ (M.node i) c, yUnit_mem_adjointGroup _ _, M.toGeck_yUnit ℚ i c⟩
  have hv := (mem_fracVanishingIdeal _ x).mp hx ⟨_, M.pointsMulEquiv_symm_toGeck_mem g hg⟩
  simp only [hgeq, DynkinType.coe_geckRootSubgroupPoints] at hv
  have hpt := UniversalEnvelopingAlgebra.pointsMulEquiv_kostantRootSubgroupCoordinateMap
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) j
    (t.isNilpotent_geckRepresentation_rootGenerator ht j) (t.geckCoordinateBasisFin ht) ℚ
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := ℚ)).symm (Multiplicative.ofAdd c))
  rw [← hpt, GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_pointToGeneralLinear] at hv
  exact hv

theorem eval_eq_zero_of_mem_nativeVanishingIdeal
    (hgen : t.geckDefiningIdeal ht = UniversalEnvelopingAlgebra.kostantGeneratedDefiningIdeal
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht) (t.geckCoordinateBasisFin ht))
    (A : Type) [CommRing A] (g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A)
    (hg : g ∈ t.geckPoints ht A) (x : GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
    (hx : x ∈ M.nativeVanishingIdeal) :
    ((GeneralLinear.pointsMulEquiv (R := ℤ) (t.geckDim ht)).symm g).ofConv x = 0 :=
  (t.mem_geckPoints_iff ht A g).mp hg x (M.nativeVanishingIdeal_le_geckDefiningIdeal hgen hx)

theorem aeval_eq_zero_of_forall_adjointGroup
    (hgen : t.geckDefiningIdeal ht = UniversalEnvelopingAlgebra.kostantGeneratedDefiningIdeal
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht) (t.geckCoordinateBasisFin ht))
    (P : MvPolynomial (Fin (t.geckDim ht) × Fin (t.geckDim ht)) ℤ)
    (hP : ∀ g ∈ adjointGroup τ ℚ, MvPolynomial.aeval
      (fun ij : Fin (t.geckDim ht) × Fin (t.geckDim ht) =>
        ((M.toGeck ℚ g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) ℚ) :
          Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) ℚ) ij.1 ij.2) P = 0)
    (A : Type) [CommRing A] (g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A)
    (hg : g ∈ t.geckPoints ht A) :
    MvPolynomial.aeval (fun ij : Fin (t.geckDim ht) × Fin (t.geckDim ht) =>
      (g : Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) ij.1 ij.2) P = 0 := by
  have hx : GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ (t.geckDim ht)
      (GeneralLinear.coordinateRingMap ℤ (t.geckDim ht) P) ∈ M.nativeVanishingIdeal := by
    refine (mem_fracVanishingIdeal _ _).mpr ?_
    rintro ⟨_, ⟨_, ⟨g', hg', rfl⟩, rfl⟩⟩
    change ((GeneralLinear.pointsMulEquiv (R := ℤ) (t.geckDim ht)).symm
      (M.toGeck ℚ g')).ofConv _ = 0
    rw [GeneralLinear.pointsMulEquiv_symm_apply,
      GeneralLinear.generalLinearToPoint_coordinateRingMap]
    exact hP g' hg'
  have := M.eval_eq_zero_of_mem_nativeVanishingIdeal hgen A g hg _ hx
  rwa [GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_coordinateRingMap] at this

end GeckMatch

end CFSG.TauCetiBridge
