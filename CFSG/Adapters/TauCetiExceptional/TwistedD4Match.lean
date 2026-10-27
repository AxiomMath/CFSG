module

public import CFSG.Adapters.TauCetiExceptional.TwistedD4Data
public import CFSG.Adapters.TauCetiExceptional.MinusculeClosure
public import CFSG.Adapters.TauCetiExceptional.MinusculeCell
public import TauCeti.Algebra.Lie.D4.Tripled.Generation
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.TripledWeight

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule TauCeti
  TauCeti.UniversalEnvelopingAlgebra WithConv
open CFSG.TauCetiBridge.Minuscule

@[expose] def d4Node : Fin 4 ≃ Fin (Tag.rank .D4) := Equiv.swap (1 : Fin 4) 2

theorem d4_cartan (i j : Fin 4) :
    D4Tripled.weightTable.cartanMatrix i j = Tag.cartan .D4 (d4Node i) (d4Node j) := by
  rw [D4Tripled.weightTable_cartanMatrix]
  fin_cases i <;> fin_cases j <;> rfl

theorem d4Node_trialityPermD4 (i : Fin 4) :
    d4Node (trialityPermD4 i) = TwistTag.D4.perm (d4Node i) := by
  fin_cases i
  · rw [show ((fun i => i) ⟨0, by decide⟩ : Fin 4) = 0 from rfl, trialityPermD4_apply_zero]
    rfl
  · rw [show ((fun i => i) ⟨1, by decide⟩ : Fin 4) = 1 from rfl, trialityPermD4_apply_one]
    rfl
  · rw [show ((fun i => i) ⟨2, by decide⟩ : Fin 4) = 2 from rfl, trialityPermD4_apply_two]
    rfl
  · rw [show ((fun i => i) ⟨3, by decide⟩ : Fin 4) = 3 from rfl, trialityPermD4_apply_three]
    rfl

@[expose] def d4LabFun : Fin 24 → Fin 24 :=
  ![0, 3, 6, 9, 10, 15, 18, 21, 1, 4, 7, 11, 12, 16, 19, 22, 2, 5, 8, 13, 14, 17, 20, 23]

@[expose] def d4LabInv : Fin 24 → Fin 24 :=
  ![0, 8, 16, 1, 9, 17, 2, 10, 18, 3, 4, 11, 12, 19, 20, 5, 13, 21, 6, 14, 22, 7, 15, 23]

@[expose] def d4Lab : Fin 24 ≃ Fin d4tData.d where
  toFun := d4LabFun
  invFun := d4LabInv
  left_inv x := by fin_cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

theorem d4_wt_lab (a : Fin 24) (i : Fin 4) :
    d4tData.wt (d4Lab a) (d4Node i) = D4Tripled.weightTable.weight a i := by
  rw [D4Tripled.weightTable_weight]
  revert a i
  decide +kernel

@[expose] def d4Match : WeightMatch d4tData D4Tripled.weightTable :=
  ⟨d4Node, d4Lab, d4_wt_lab, d4_cartan⟩

theorem d4_rootSubgroupPoints_inl
    (A : Type*) [CommRing A] (i : Fin 4) (c : A) :
    (D4Tripled.rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 24) A) =
      toMat d4Match.lab A (rootUnit d4tData_valid A (Pi.single (d4Match.node i) 1) c) := by
  refine Units.ext ?_
  rw [D4Tripled.coe_rootSubgroupPoints_inl, toAdd_ofAdd, D4Tripled.raisingMatrix_def]
  exact (d4Match.toMat_rootUnit_single d4tData_valid A i c).symm

theorem d4_rootSubgroupPoints_inr
    (A : Type*) [CommRing A] (i : Fin 4) (c : A) :
    (D4Tripled.rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 24) A) =
      toMat d4Match.lab A (rootUnit d4tData_valid A (-Pi.single (d4Match.node i) 1) c) := by
  refine Units.ext ?_
  rw [D4Tripled.coe_rootSubgroupPoints_inr, toAdd_ofAdd, D4Tripled.loweringMatrix_def]
  exact (d4Match.toMat_rootUnit_neg_single d4tData_valid A i c).symm

theorem d4_toMat_mem_points
    (K : Type*) [Field K] (g : d4tData_valid.minGroup K) :
    toMat d4Match.lab K g ∈ D4Tripled.points K := by
  refine toMat_mem_of_simple d4tData_valid d4Match.lab K (P := D4Tripled.points K)
    (fun i c => ?_) g
  obtain ⟨i, rfl⟩ := d4Match.node.surjective i
  constructor
  · rw [← rootUnit_eq_xu, ← d4_rootSubgroupPoints_inl]
    exact (D4Tripled.rootSubgroupPoints (.inl i) K (Multiplicative.ofAdd c)).2
  · rw [← rootUnit_eq_xu, ← d4_rootSubgroupPoints_inr]
    exact (D4Tripled.rootSubgroupPoints (.inr i) K (Multiplicative.ofAdd c)).2

@[expose] def d4RatPoints :
    Subgroup (WithConv (GeneralLinear.coordinateHopfAlgebra ℤ 24 →ₐ[ℤ] ℚ)) :=
  ((d4tData_valid.minGroup ℚ).map (toMat d4Match.lab ℚ).toMonoidHom).map
    (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 24).symm.toMonoidHom

@[expose] def d4NativeVanishingIdeal :
    HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ 24) :=
  fracVanishingIdeal (R := ℤ) (K := ℚ) d4RatPoints

theorem pointsMulEquiv_symm_toMat_mem_d4RatPoints
    (g : d4tData_valid.minGroup ℚ) :
    (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 24).symm (toMat d4Match.lab ℚ g) ∈
      d4RatPoints :=
  ⟨toMat d4Match.lab ℚ g, ⟨g, g.2, rfl⟩, rfl⟩

theorem d4NativeVanishingIdeal_le_definingIdeal :
    d4NativeVanishingIdeal ≤ D4Tripled.definingIdeal := by
  rw [D4Tripled.definingIdeal_eq_kostantGeneratedDefiningIdeal]
  refine fracVanishingIdeal_le_kostantGeneratedDefiningIdeal _ _ _ _ _ _ _ _ fun j c => ?_
  rw [← D4Tripled.coe_rootSubgroupPoints]
  rcases j with i | i
  · rw [d4_rootSubgroupPoints_inl, rootUnit_eq_xu]
    exact pointsMulEquiv_symm_toMat_mem_d4RatPoints ⟨_, d4tData_valid.xu_mem ℚ _ c⟩
  · rw [d4_rootSubgroupPoints_inr, rootUnit_eq_xu]
    exact pointsMulEquiv_symm_toMat_mem_d4RatPoints ⟨_, d4tData_valid.xu_mem ℚ _ c⟩

theorem d4_evalMat_eq_zero
    (P : MvPolynomial (Fin 24 × Fin 24) ℤ)
    (hP : ∀ g : d4tData_valid.minGroup ℚ,
      BigCell.evalMat ((toMat d4Match.lab ℚ g : Matrix.GeneralLinearGroup (Fin 24) ℚ) :
        Matrix (Fin 24) (Fin 24) ℚ) P = 0)
    (A : Type*) [CommRing A] (g : Matrix.GeneralLinearGroup (Fin 24) A)
    (hg : g ∈ D4Tripled.points A) :
    BigCell.evalMat (g : Matrix (Fin 24) (Fin 24) A) P = 0 := by
  have hx : GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ 24
      (GeneralLinear.coordinateRingMap ℤ 24 P) ∈ d4NativeVanishingIdeal := by
    refine (mem_fracVanishingIdeal _ _).mpr ?_
    rintro ⟨_, ⟨_, ⟨g', hg', rfl⟩, rfl⟩⟩
    change ((GeneralLinear.pointsMulEquiv (R := ℤ) 24).symm
      (toMat d4Match.lab ℚ g')).ofConv _ = 0
    rw [GeneralLinear.pointsMulEquiv_symm_apply,
      GeneralLinear.generalLinearToPoint_coordinateRingMap, aeval_eq_evalMat]
    exact hP ⟨g', hg'⟩
  have := (D4Tripled.mem_points_iff A g).mp hg _ (d4NativeVanishingIdeal_le_definingIdeal hx)
  rwa [GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_coordinateRingMap, aeval_eq_evalMat] at this

theorem d4_evalMat_eq_zero_of_root_subgroups
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 24) ℚ))
    (hH : ∀ (j : Fin 4 ⊕ Fin 4) (c : ℚ),
      (D4Tripled.rootSubgroupPoints j ℚ (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 24) ℚ) ∈ H)
    (P : MvPolynomial (Fin 24 × Fin 24) ℤ)
    (hP : ∀ g ∈ H, BigCell.evalMat (g : Matrix (Fin 24) (Fin 24) ℚ) P = 0)
    (A : Type*) [CommRing A] (g : Matrix.GeneralLinearGroup (Fin 24) A)
    (hg : g ∈ D4Tripled.points A) :
    BigCell.evalMat (g : Matrix (Fin 24) (Fin 24) A) P = 0 := by
  let S := H.map (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 24).symm.toMonoidHom
  have hle : fracVanishingIdeal (R := ℤ) (K := ℚ) S ≤ D4Tripled.definingIdeal := by
    rw [D4Tripled.definingIdeal_eq_kostantGeneratedDefiningIdeal]
    refine fracVanishingIdeal_le_kostantGeneratedDefiningIdeal _ _ _ _ _ _ _ _ fun j c => ?_
    rw [← D4Tripled.coe_rootSubgroupPoints]
    exact ⟨_, hH j c, rfl⟩
  have hx : GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ 24
      (GeneralLinear.coordinateRingMap ℤ 24 P) ∈ fracVanishingIdeal (R := ℤ) (K := ℚ) S := by
    refine (mem_fracVanishingIdeal _ _).mpr ?_
    rintro ⟨_, ⟨g', hg', rfl⟩⟩
    change ((GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 24).symm g').ofConv
      (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ 24
        (GeneralLinear.coordinateRingMap ℤ 24 P)) = 0
    rw [GeneralLinear.pointsMulEquiv_symm_apply,
      GeneralLinear.generalLinearToPoint_coordinateRingMap, aeval_eq_evalMat]
    exact hP g' hg'
  have hzero := (D4Tripled.mem_points_iff A g).mp hg _ (hle hx)
  rwa [GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_coordinateRingMap, aeval_eq_evalMat] at hzero

theorem d4tData_degOrdered : DegOrdered d4tData := by
  unfold DegOrdered MinData.deg
  decide +kernel

theorem cartan_D4_eq_submatrix :
    Tag.cartan .D4 = (CartanMatrix.D 4).submatrix d4Node.symm d4Node.symm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem posDef_cartan_D4 : ((Tag.cartan .D4).map (Int.cast : ℤ → ℚ)).PosDef := by
  rw [cartan_D4_eq_submatrix, ← Matrix.submatrix_map]
  exact (posDef_map_intCast_cartanMatrix_D 4).submatrix d4Node.symm.injective

end CFSG.TauCetiBridge.Twisted
