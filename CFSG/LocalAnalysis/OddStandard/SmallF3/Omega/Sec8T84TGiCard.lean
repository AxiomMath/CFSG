module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IVAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec8t84t_gi_cent_card (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {ρ : ↥(simGroup Q)} (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    Nat.card ↥(fixSub (simAct Q ρ)) = 1440 := by
  haveI : Fact (¬ IsSquare (-1 : ZMod 3)) := ⟨by decide⟩
  haveI : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := ZMod 3) (by rw [hdim]; norm_num)
  let T : Module.End (ZMod 3) V := ((ρ : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V)
  have hns : ¬ IsSquare (-1 : ZMod 3) := by decide
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hd : (-1 : ZMod 3) ≠ 0 := by decide
  have hsquare : T ^ 2 = algebraMap (ZMod 3) (Module.End (ZMod 3) V) (-1) :=
    ff_aux_hsquare hρρ
  have hadj : ∀ x y, Q.polarBilin (T x) y = Q.polarBilin x (T y) := ff_aux_hadj hρ hρρ
  have hQp : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  letI : Field (scalarAlgebra T) := scalarField T (-1) hns hsquare
  letI : Module (scalarAlgebra T) V := evaluationModule T
  haveI : IsScalarTower (ZMod 3) (scalarAlgebra T) V := evaluationScalarTower T
  haveI : Module.Finite (ZMod 3) (scalarAlgebra T) := scalarAlgebra_finite T (-1) hns hsquare
  haveI : Finite (scalarAlgebra T) := Module.finite_of_finite (ZMod 3)
  have hfin := scalar_square_actual_finite_dimension (K := ZMod 3) (V := V) T (-1) hns hsquare
  haveI : Module.Finite (scalarAlgebra T) V := hfin.1
  haveI : CharP (scalarAlgebra T) 3 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 3) (scalarAlgebra T)).injective 3
  let QE : QuadraticForm (scalarAlgebra T) V :=
    actualPositiveQuadratic Q T (-1) hd hns hsquare hadj
  obtain ⟨-, -, -, hQEnd, -, -, e1, -, -, -, -⟩ :=
    positive_nonsquare_centralizer_structure Q hQp T (-1) hd hns hsquare h2 hadj
  have hdimK : Module.finrank (scalarAlgebra T) V = 3 := by rw [hfin.2.2, hdim]
  have hcard : Nat.card (scalarAlgebra T) = 3 ^ 2 := by
    rw [scalarAlgebra_card T (-1) hns hsquare, Nat.card_zmod]
  have hchar : ringChar (scalarAlgebra T) = 3 := ringChar.eq (scalarAlgebra T) 3
  have h2K : ringChar (scalarAlgebra T) ≠ 2 := by rw [hchar]; decide
  have hord := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd
    (K := scalarAlgebra T) (V := V) h2K hQEnd (n := 1) (by rw [hdimK])
  have hgoal : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup QE) : ℤ) = 1440 := by
    rw [hord, hcard]
    decide
  have hcardO : Nat.card ↥(orthogonalOperatorCentralizer Q T) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup QE) :=
    Nat.card_congr e1.toEquiv
  have hGc_eq : orthogonalOperatorCentralizer Q T = fixSub (simAct Q ρ) :=
    (ff_aux_fixSub_eq).symm
  rw [← hGc_eq, hcardO]
  exact_mod_cast hgoal

end CFSG.OddStandard.SmallF3.Omega
