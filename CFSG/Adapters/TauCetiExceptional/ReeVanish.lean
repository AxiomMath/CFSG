module

public import CFSG.Adapters.TauCetiExceptional.FrameworkClosure
public import CFSG.Adapters.TauCetiExceptional.BigCellCore
public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Generation
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open TauCeti TauCeti.G2ShortRoot TauCeti.UniversalEnvelopingAlgebra WithConv
open CFSG.TauCetiBridge.BigCell

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

local notation "CM" => CartanMatrix.G₂
local notation "rootGen" => TauCeti.serreRootGenerator CM
local notation "cartanGen" => TauCeti.serreH ℚ CM

@[expose] def ratRootGroup : Subgroup (Matrix.GeneralLinearGroup (Fin 7) ℚ) :=
  Subgroup.closure {g | ∃ (k : Fin 2 ⊕ Fin 2) (t : ℚ), g =
    (IntegralToralClosure.rootSubgroupPoints k ℚ (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 7) ℚ)}

theorem rootPoint_mem_ratRootGroup (k : Fin 2 ⊕ Fin 2) (t : ℚ) :
    (IntegralToralClosure.rootSubgroupPoints k ℚ (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 7) ℚ) ∈ ratRootGroup :=
  Subgroup.subset_closure ⟨k, t, rfl⟩

@[expose] def ratRootPoints :
    Subgroup (WithConv (GeneralLinear.coordinateHopfAlgebra ℤ 7 →ₐ[ℤ] ℚ)) :=
  ratRootGroup.map (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 7).symm.toMonoidHom

@[expose] def ratVanishingIdeal : HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ 7) :=
  fracVanishingIdeal (R := ℤ) (K := ℚ) ratRootPoints

theorem ratVanishingIdeal_le_definingIdeal :
    ratVanishingIdeal ≤ IntegralToralClosure.definingIdeal := by
  rw [IntegralToralClosure.definingIdeal_eq_kostantGeneratedDefiningIdeal,
    le_kostantGeneratedDefiningIdeal_iff]
  intro k x hx
  rw [RingHom.mem_ker]
  apply symmetricAlgebra_eq_zero_of_forall_rat
  intro c
  have hmem : (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 7).symm
      (IntegralToralClosure.rootSubgroupPoints k ℚ (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 7) ℚ) ∈ ratRootPoints :=
    ⟨_, rootPoint_mem_ratRootGroup k c, rfl⟩
  have hv := (mem_fracVanishingIdeal _ x).mp hx ⟨_, hmem⟩
  simp only [IntegralToralClosure.coe_rootSubgroupPoints_eq_kostantRootSubgroupMatrix] at hv
  have hpt := pointsMulEquiv_kostantRootSubgroupCoordinateMap rootGen cartanGen rep
    lattice.toAddSubgroup rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k)
    latticeBasis ℚ ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := ℚ)).symm
      (Multiplicative.ofAdd c))
  rw [← hpt, GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_pointToGeneralLinear] at hv
  exact hv

theorem evalMat_eq_aeval {A : Type*} [CommRing A] (M : Matrix (Fin 7) (Fin 7) A)
    (P : MvPolynomial (Fin 7 × Fin 7) ℤ) :
    evalMat M P = MvPolynomial.aeval (fun ij : Fin 7 × Fin 7 => M ij.1 ij.2) P := by
  rw [evalMat, MvPolynomial.aeval_def, algebraMap_int_eq]
  rfl

theorem evalMat_eq_zero_of_mem_points (P : MvPolynomial (Fin 7 × Fin 7) ℤ)
    (hP : ∀ s ∈ ratRootGroup, evalMat (s : Matrix (Fin 7) (Fin 7) ℚ) P = 0)
    {A : Type} [CommRing A] [Algebra (ZMod 3) A] {g : Matrix.GeneralLinearGroup (Fin 7) A}
    (hg : g ∈ PrimeField.points A) : evalMat (g : Matrix (Fin 7) (Fin 7) A) P = 0 := by
  have hy : GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ 7
      (GeneralLinear.coordinateRingMap ℤ 7 P) ∈ ratVanishingIdeal := by
    refine (mem_fracVanishingIdeal _ _).mpr ?_
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    change ((GeneralLinear.pointsMulEquiv (R := ℤ) 7).symm s).ofConv _ = 0
    rw [GeneralLinear.pointsMulEquiv_symm_apply,
      GeneralLinear.generalLinearToPoint_coordinateRingMap, ← evalMat_eq_aeval]
    exact hP s hs
  have hy' := ratVanishingIdeal_le_definingIdeal hy
  rw [IntegralToralClosure.definingIdeal_def] at hy'
  have hz := map_tmul_mem_kostantToralBaseChangePresentationIdeal_of_mem rootGen cartanGen rep
    lattice.toAddSubgroup rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator
    latticeBasis weight (ZMod 3) (1 : ZMod 3) hy'
  have hgp := PrimeField.points_le_baseChangePresentationPoints A hg
  rw [GeneralLinear.mem_hopfIdealPointsSubgroup_iff] at hgp
  have h0 := hgp _ hz
  rw [GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply, one_smul,
    GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_coordinateRingMap,
    MvPolynomial.aeval_map_algebraMap] at h0
  rw [evalMat_eq_aeval]
  exact h0

end CFSG.TauCetiBridge.Ree
