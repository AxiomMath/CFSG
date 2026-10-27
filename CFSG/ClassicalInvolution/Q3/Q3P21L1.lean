module

public import CFSG.ClassicalInvolution.Q3.Q3TLKSp
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.Q3.Q3TCBridge
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSL
public import CFSG.ClassicalInvolution.Q3.Q3TIVSm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TWZ CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.ModelFacts.TG3
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TLK
  CFSG.ClassicalInvolution.Q3.Q3TY
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinDatumOn TwinMFGenerationOn)
open CFSG.ClassicalInvolution.Q3 (CompData)
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


section Model

theorem eq_of_isLongRootSL2_sl4 {R R' : Subgroup SL(4, 𝔽₃)} {i i' : SL(4, 𝔽₃)}
    (h₁ : Models.IsLongRootSL2 (show 2 ≤ 4 by norm_num) R i)
    (h₂ : Models.IsLongRootSL2 (show 2 ≤ 4 by norm_num) R' i') (h : i = i') : R = R' := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  rw [h₁.eq_longRootGroup h2, h₂.eq_longRootGroup h2, h]

theorem twinDatum_ne_psl4 {R R' : Subgroup (Generic.modelUniv .PSL 4 3 1 Nat.prime_three).K}
    {x x' : (Generic.modelUniv .PSL 4 3 1 Nat.prime_three).K}
    (hd : TwinDatumOn .PSL (Generic.modelUniv .PSL 4 3 1 Nat.prime_three) R R' x x') : x ≠ x' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hadm : StatedLieAdmissible .PSL 4 3 1 := Q3TC.statedLieAdmissible_sl4_three
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (t := .PSL)
    (n := 4) (by norm_num) trivial hadm (by decide) (by decide) hd.mem
  obtain ⟨e₂⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (t := .PSL)
    (n := 4) (by norm_num) trivial hadm (by decide) (by decide) hd.mem'
  have hx : x = Asc77.sl2Inv e₁ := eq_sl2Inv_of_central3 e₁ hd.hx hd.cx hd.nx
  have hx' : x' = Asc77.sl2Inv e₂ := eq_sl2Inv_of_central3 e₂ hd.hx' hd.cx' hd.nx'
  intro hxx
  apply hd.ne
  have h₁ := isLongRootSL2_sl2Inv_four hd.mem e₁
  have h₂ := isLongRootSL2_sl2Inv_four hd.mem' e₂
  exact eq_of_isLongRootSL2_sl4 h₁ h₂ (hx.symm.trans (hxx.trans hx'))

theorem twinMFGenerationOn3_psl4 :
    TwinMFGenerationOn .PSL (Generic.modelUniv .PSL 4 3 1 Nat.prime_three) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact twinMFGenerationOn3_of_strong (t := .PSL) trivial Q3TC.statedLieAdmissible_sl4_three
    (by decide) (by decide) (by decide) Q3Y2.twinStrong3_psl_four fun hd => twinDatum_ne_psl4 hd

end Model

section Trichotomy

theorem sqTrichotomy3_minus4 :
    SqTrichotomyOn .POmegaMinus (Generic.modelUniv .POmegaMinus 4 3 1 Nat.prime_three) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn4 : 4 ≤ 4 := le_rfl
  have he : 1 ≤ 1 := le_rfl
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hdim : Module.finrank 𝔽₃ (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → 𝔽₃) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) :=
    isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr 3 1)
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have cq := centralQuot3_minus hadm
  have hZ3 : ∀ c ∈ Subgroup.center (spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)), ¬ 3 ∣ orderOf c :=
    (powCop3_model (t := .POmegaMinus) (n := 4) trivial hadm (by decide) (by decide)).cop
  show SqTrichotomyOn .POmegaMinus ⟨spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2), Twisted.minusDatum 4 (minusCoeffs_irr 3 1)⟩
  intro X _ θ hθs hθk R R' R₂ hR hR' hR₂ hne x x' x₂ hx hx2 hx1 hx' hx'2 hx'1 hxx' hx₂ hx₂2 hx₂1
    α hα4 hαR hαR' hαR₂
  exact spin_sq_trichotomy3 odd_gf3 card_gf3
    (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr 3 1))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr 3 1))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr 3 1)) hZ3 (by omega)
    (fun F₁ F₂ h => hproj_minus (minusCoeffs_irr 3 1) hn4 F₁ F₂ h)
    (fun F₀ F₁ h => false_of_orth_quadMinus_four3 h2 (minusCoeffs_irr 3 1)
      (by rw [card_gf3]; norm_num) F₀ F₁ h)
    hθs hθk (Asc77.liftSim_quadMinus hp2 hn4 he θ hθk) (fun e => cq.map_inj hR hR' e)
    (cq.map_mem R hR) (cq.map_mem R' hR') (cq.inj R hR) (cq.inj R' hR') hne hx hx2 hx1 hx' hx'2
    hx'1 hxx'
    (cq.pow3 R₂ hR₂) (cq.map_mem R₂ hR₂) (cq.inj R₂ hR₂) hx₂ hx₂2 hx₂1 α hα4 hαR hαR' hαR₂

end Trichotomy

end CFSG.ClassicalInvolution.Q3.Q3P21
