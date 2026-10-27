module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFBase
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSim
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFStd
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFGCase
public import CFSG.ClassicalInvolution.Q3.Q3MFOSOdd
public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.ModelFacts.TG3Common
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Tags
public import CFSG.ClassicalInvolution.Q3.Q3MFODHyp
public import CFSG.ClassicalInvolution.Q3.Q3NMM11
public import CFSG.ClassicalInvolution.Q3.Q3NMSl23
public import CFSG.ClassicalInvolution.Q3.Q3TIRed

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

theorem sl3_facts
    {n : ℕ} (hn : 3 ≤ n) :
    CFSG.Open.IsQuasisimple SL(n, 𝔽₃) ∧ IsPGroup 2 (Subgroup.center SL(n, 𝔽₃)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hadmL : StatedLieAdmissible .PSL (m + 1) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega,
      fun h => by have := congrArg Prod.fst h; simp only at this; omega,
      fun h => by have := congrArg Prod.fst h; simp only at this; omega⟩
  exact ⟨(ModelFacts.modelClauseZero .PSL (m + 1) 3 1 Nat.prime_three trivial hadmL).1,
    (modelFiniteCenterTwoGroup3 .PSL (m + 1) Nat.prime_three trivial hadmL).2⟩

section Spin

theorem fixedOddFree_spinPlus {k : ℕ} (hk : 5 ≤ k) [Finite (spinGroup (quadPlus k 𝔽₃))]
    (hZ2 : IsPGroup 2 (Subgroup.center (spinGroup (quadPlus k 𝔽₃))))
    (hSL : CFSG.Open.IsQuasisimple SL(k, 𝔽₃)) (hSLZ : IsPGroup 2 (Subgroup.center SL(k, 𝔽₃))) :
    FixedOddFree (spinGroup (quadPlus k 𝔽₃) ⧸ Subgroup.center (spinGroup (quadPlus k 𝔽₃))) := by
  have hn3 : 3 ≤ k := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : Nat.card 𝔽₃ = 3 := ModelFacts.TG3.natCard_galoisField_three
  have : Group.IsPerfect (spinGroup (quadPlus k 𝔽₃)) := isPerfect_spinGroup_quadPlus hn3
  have hQ := nondegenerate_polarBilin_quadPlus k 𝔽₃
  have hdim : Module.finrank 𝔽₃ (Fin k ⊕ Fin k → 𝔽₃) = 2 * k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hEq := (commutator_orthogonalGroup_quadPlus (K := 𝔽₃) hn3).symm
  refine fixedOddFree_of_spin3 hF3 hQ (by omega) (range_spinAction_quadPlus (K := 𝔽₃) hn3) hEq
    (Asc77.liftSim_quadPlus (p := 3) (e := 1) (by norm_num) hk le_rfl _
      (by rw [QuotientGroup.ker_mk']))
    (ModelFacts.open_isQuasisimple (isQuasisimple_spinGroup_quadPlus hn3)) hZ2 ?_
  intro a hg ha
  rcases ha with ha | ha
  · exact oddCoreIn_fixed_conjES_of_sim_involution_n hF3 (by omega) hSL hSLZ hQ hEq ha hg
  · exact Gauss.oddCoreIn_fixed_conjES_of_sq_neg_one hF3 hQ hEq ha hg (Or.inl (by omega))

theorem fixedOddFree_spinMinus {k : ℕ} (hk : 4 ≤ k)
    [Finite (spinGroup (quadMinus k 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))]
    (hZ2 : IsPGroup 2
      (Subgroup.center (spinGroup (quadMinus k 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)))) :
    FixedOddFree (spinGroup (quadMinus k 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) ⧸
      Subgroup.center (spinGroup (quadMinus k 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : Nat.card 𝔽₃ = 3 := ModelFacts.TG3.natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF3
  have hirr := minusCoeffs_irr 3 1
  have : Group.IsPerfect (spinGroup (quadMinus k 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) :=
    isPerfect_spinGroup_quadMinus hk hirr
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite k 𝔽₃ hirr
  have hdim : Module.finrank 𝔽₃ (Fin (k - 1) ⊕ Fin (k - 1) ⊕ Fin 2 → 𝔽₃) = 2 * k := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hEq := (commutator_orthogonalGroup_quadMinus hk hirr).symm
  refine fixedOddFree_of_spin3 hF3 hQ (by omega) (range_spinAction_quadMinus hk hirr) hEq
    (Asc77.liftSim_quadMinus (p := 3) (e := 1) (by norm_num) hk le_rfl _
      (by rw [QuotientGroup.ker_mk']))
    (ModelFacts.open_isQuasisimple (isQuasisimple_spinGroup_quadMinus hk hirr)) hZ2 ?_
  intro a hg ha
  rcases ha with ha | ha
  · exact (false_of_sim_involution_minus h2 hirr (by rw [hF3]; norm_num) (by omega) hQ ha
      (fun v => by rw [hg v, neg_one_mul])).elim
  · refine Gauss.oddCoreIn_fixed_conjES_of_sq_neg_one hF3 hQ hEq ha hg ?_
    rcases Nat.lt_or_ge k 5 with hk5 | hk5
    · right
      obtain rfl : k = 4 := by omega
      exact ⟨by rw [hdim], fun v hv =>
        Q3MFOD.false_of_isHypFam_quadMinus h2 hirr (by rw [hF3]; norm_num) v hv⟩
    · left
      omega

end Spin

section Model


theorem fixedOddFree_of_lieModel_pOmegaPlus {k : ℕ} (hk : 5 ≤ k) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hS : LieModel S .POmegaPlus k 3 1) : FixedOddFree S := by
  have hFT : IsFundTag StatedLieTag.POmegaPlus := trivial
  have hadm : StatedLieAdmissible .POmegaPlus k 3 1 := ⟨Nat.prime_three, le_rfl, by omega⟩
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover _ k 3 1 Nat.prime_three (by norm_num) hFT hadm S hS
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := center_eq_bot_of_isQuasisimple hSq
  have : Group.IsPerfect (modelUniv .POmegaPlus k 3 1 Nat.prime_three).K :=
    ⟨((ModelFacts.modelClauseZero .POmegaPlus k 3 1 Nat.prime_three hFT hadm).1).1⟩
  have hfz := modelFiniteCenterTwoGroup3 .POmegaPlus k Nat.prime_three hFT hadm
  obtain ⟨hSL, hSLZ⟩ := sl3_facts (n := k) (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn3 : 3 ≤ k := by omega
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus k 𝔽₃), plusDatum k 𝔽₃ hn3⟩ →
      Finite M.K ∧ IsPGroup 2 (Subgroup.center M.K) →
      FixedOddFree (M.K ⧸ Subgroup.center M.K) := by
    intro M hM hMf
    subst hM
    have := hMf.1
    exact fixedOddFree_spinPlus hk hMf.2 hSL hSLZ
  have hM : modelUniv .POmegaPlus k 3 1 Nat.prime_three =
      ⟨spinGroup (quadPlus k 𝔽₃), plusDatum k 𝔽₃ hn3⟩ := by
    simp only [modelUniv, CFSG.LieType.Universal.lieUniversal, hn3, ↓reduceDIte]
  let e : S ≃* (modelUniv .POmegaPlus k 3 1 Nat.prime_three).K ⧸
      Subgroup.center (modelUniv .POmegaPlus k 3 1 Nat.prime_three).K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (Q3NM.centralQuotientIso ψ hψ hker).symm
  exact Q3MFO.fixedOddFree_of_mulEquiv e (key _ hM hfz)

theorem fixedOddFree_of_lieModel_pOmegaMinus {k : ℕ} (hk : 4 ≤ k) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hS : LieModel S .POmegaMinus k 3 1) : FixedOddFree S := by
  have hFT : IsFundTag StatedLieTag.POmegaMinus := trivial
  have hadm : StatedLieAdmissible .POmegaMinus k 3 1 := ⟨Nat.prime_three, le_rfl, hk⟩
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover _ k 3 1 Nat.prime_three (by norm_num) hFT hadm S hS
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := center_eq_bot_of_isQuasisimple hSq
  have : Group.IsPerfect (modelUniv .POmegaMinus k 3 1 Nat.prime_three).K :=
    ⟨((ModelFacts.modelClauseZero .POmegaMinus k 3 1 Nat.prime_three hFT hadm).1).1⟩
  have hfz := modelFiniteCenterTwoGroup3 .POmegaMinus k Nat.prime_three hFT hadm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hirr := minusCoeffs_irr 3 1
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadMinus k 𝔽₃ (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2), Twisted.minusDatum k hirr⟩ →
      Finite M.K ∧ IsPGroup 2 (Subgroup.center M.K) →
      FixedOddFree (M.K ⧸ Subgroup.center M.K) := by
    intro M hM hMf
    subst hM
    have := hMf.1
    exact fixedOddFree_spinMinus hk hMf.2
  have hM : modelUniv .POmegaMinus k 3 1 Nat.prime_three = ⟨spinGroup (quadMinus k 𝔽₃
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2), Twisted.minusDatum k hirr⟩ := by
    simp only [modelUniv, CFSG.LieType.Universal.lieUniversal]
  let e : S ≃* (modelUniv .POmegaMinus k 3 1 Nat.prime_three).K ⧸
      Subgroup.center (modelUniv .POmegaMinus k 3 1 Nat.prime_three).K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (Q3NM.centralQuotientIso ψ hψ hker).symm
  exact Q3MFO.fixedOddFree_of_mulEquiv e (key _ hM hfz)

theorem outerFixedOddFree_pOmegaPlus {k : ℕ} (hk : 5 ≤ k) : OuterFixedOddFree .POmegaPlus k :=
  fun _ _ _ _ hS σ hσ _ => fixedOddFree_of_lieModel_pOmegaPlus hk hS σ hσ

theorem outerFixedOddFree_pOmegaMinus {k : ℕ} (hk : 4 ≤ k) : OuterFixedOddFree .POmegaMinus k :=
  fun _ _ _ _ hS σ hσ _ => fixedOddFree_of_lieModel_pOmegaMinus hk hS σ hσ

end Model

end CFSG.ClassicalInvolution.Q3.TL4
