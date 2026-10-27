module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairLinearTorus
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Matrix LinearAlgebra.Projectivization

theorem linear_model_action_point_and_pair (f : ℕ) (hf : 2 ≤ f) :
    let K := BinaryGaloisField f
    let Omega := ℙ K (Fin 2 → K)
    let G := Matrix.ProjGenLinGroup (Fin 2) K
    ∃ (rho : G →* Equiv.Perm Omega) (b : Omega) (B : Subgroup G),
      (∀ (g : G) (z : Omega) (A : GL (Fin 2) K),
        Matrix.ProjGenLinGroup.mk A = g →
          rho g z = (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z) ∧
      letI : MulAction G Omega := MulAction.compHom Omega rho
      B = MulAction.stabilizer G b ∧ TwoRankAtLeastTwo G ∧ fusionStronglyEmbedded B ∧
      MulAction.IsMultiplyPretransitive G Omega 2 ∧
      Nat.card {x : G // x ∈ B ∧ IsInvolution x} = 2 ^ f - 1 ∧
      ∃ (a0 b0 : Omega) (w : G) (T0 : Subgroup G),
        a0 ≠ b0 ∧ w • a0 = b0 ∧ w • b0 = a0 ∧
        (T0 : Set G) = {x | x • a0 = a0 ∧ x • b0 = b0} ∧
        IsCyclic T0 ∧ Nat.card T0 = 2 ^ f - 1 ∧
        ∀ x ∈ T0, rightConjugateElem x w = x⁻¹ := by
  let K := BinaryGaloisField f
  let Omega := ℙ K (Fin 2 → K)
  let G := Matrix.ProjGenLinGroup (Fin 2) K
  classical
  let : Fintype K := Fintype.ofFinite K
  let : Finite G := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨rho, b, S, hrho, hproperties⟩ := linear_natural_action_standard_pair f hf
  refine ⟨rho, b, (MulAction.stabilizer (Equiv.Perm Omega) b).comap rho, hrho, ?_⟩
  let : MulAction G Omega := MulAction.compHom Omega rho
  obtain ⟨hN, htwo, hpair⟩ := hproperties
  have hB : (MulAction.stabilizer (Equiv.Perm Omega) b).comap rho =
      MulAction.stabilizer G b := by
    ext g
    rfl
  have hdata := bender_pgl2_borel_full f hf S
  have hZcard : Nat.card (Subgroup.center (S : Subgroup G)) = 2 ^ f := hdata.2.2.2.1
  have hScard : Nat.card (S : Subgroup G) = 2 ^ f := by
    simpa only [pow_one] using hdata.2.2.2.2
  have hZtop : Subgroup.center (S : Subgroup G) = ⊤ :=
    (Subgroup.center (S : Subgroup G)).eq_top_of_card_eq (hZcard.trans hScard.symm)
  have hcentral : ∀ x : (S : Subgroup G), IsInvolution x →
      x ∈ Subgroup.center (S : Subgroup G) := by
    intro x _
    rw [hZtop]
    exact Subgroup.mem_top x
  have hrank : TwoRankAtLeastTwo G := rank_two_of_sylow_center S (by
    rw [hZcard]
    simpa only [show 2 ^ 2 = 4 from rfl] using
      Nat.pow_le_pow_right (n := 2) (by omega) hf) hdata.2.2.1
  have hSE : fusionStronglyEmbedded (MulAction.stabilizer G b) := by
    rw [← hN]
    exact hdata.1
  have hcount : Nat.card {x : G // x ∈ MulAction.stabilizer G b ∧ IsInvolution x} =
      2 ^ f - 1 := by
    rw [point_involution_card_of_sylow_center S b hN hcentral hdata.2.2.1, hZcard]
  exact ⟨hB, hrank, hB.symm ▸ hSE, htwo, hB.symm ▸ hcount, hpair⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
