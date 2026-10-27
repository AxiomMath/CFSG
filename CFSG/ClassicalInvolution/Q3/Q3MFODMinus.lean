module

public import CFSG.ClassicalInvolution.Q3.Q3MFODMain
public import CFSG.ClassicalInvolution.Q3.Q3MFODHyp
public import CFSG.ClassicalInvolution.Q3.Q3PPWireAll
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.AschTight.S19KUni
public import CFSG.ClassicalInvolution.AschTight.S19KUniFL
public import CFSG.ClassicalInvolution.Q3.Q3NHMain
public import CFSG.ClassicalInvolution.Q3.Q3OFModelU
public import CFSG.ClassicalInvolution.Q3.Q3OFProd
public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTri
public import CFSG.ClassicalInvolution.Q3.Q3OFUnique
public import CFSG.ClassicalInvolution.Q3.Q3PPInv
public import CFSG.ClassicalInvolution.Q3.Q3URDict
public import CFSG.ClassicalInvolution.Q3.Q3URStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3MFOD CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.ClassicalInvolution.Asc77 (liftSim_quadMinus)
open CFSG.ClassicalInvolution.Models.Transfer (centerScalar_quadMinus)

local notation "𝔽₃" => GaloisField 3 1


theorem fixedOddFreeFund_minus4 : FixedOddFreeFund (CompData.model .POmegaMinus 4) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨hp, le_rfl, le_rfl⟩
  have hF3 := ModelFacts.TG3.natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.TG3.two_ne_zero_three
  have hirr := minusCoeffs_irr 3 1
  have hn4 : 4 ≤ 4 := le_rfl
  have hdim : Module.finrank 𝔽₃ (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → 𝔽₃) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) :=
    isPerfect_spinGroup_quadMinus hn4 hirr
  have hfz := modelFiniteCenterTwoGroup3 .POmegaMinus 4 hp trivial hadm
  have hfin : Finite (spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) := hfz.1
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 𝔽₃ hirr
  show FixedOddFreeFund ⟨spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
    fundamentalSubgroups .POmegaMinus (Twisted.minusDatum 4 hirr)⟩
  refine fixedOddFreeFund_of_spin3 hF3 hQ (by rw [hdim]; omega)
    (range_spinAction_quadMinus hn4 hirr) (centerScalar_quadMinus hn4 hirr)
    (ModelFacts.OrthAut.minus_hker2 hirr) (commutator_orthogonalGroup_quadMinus hn4 hirr).le
    (liftSim_quadMinus (p := 3) (e := 1) (by norm_num) hn4 le_rfl _
      (by rw [QuotientGroup.ker_mk']))
    (ModelFacts.open_isQuasisimple (isQuasisimple_spinGroup_quadMinus hn4 hirr)) hfz.2
    (Q3TY.centralQuot3_minus hadm) ?_
  intro α a ha2 hsim hα
  exact (false_of_sim_involution_minus4 h2 hirr (by rw [hF3]; norm_num) hQ hdim ha2 hsim).elim

theorem mfComp_minus4 : MFComp (CompData.model .POmegaMinus 4) := Or.inr fixedOddFreeFund_minus4

end CFSG.ClassicalInvolution.Q3.Q3PP
