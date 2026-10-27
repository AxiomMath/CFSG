module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairSuzukiTorus
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairSuzukiCenter
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Matrix LinearAlgebra.Projectivization

theorem suzuki_model_action_point_and_pair (m : ℕ) (hm : 1 ≤ m) :
    let K := BinaryGaloisField (2 * m + 1)
    let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
    let pinf : ℙ K (Fin 4 → K) := Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
    let G := SuzukiMatrixGroup m
    ∃ (rho : G →* Equiv.Perm Omega) (b : Omega) (B : Subgroup G),
      (∀ (g : G) (z : Omega), ((rho g z : Omega) : ℙ K (Fin 4 → K)) =
        (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K)).toLinearEquiv •
          (z : ℙ K (Fin 4 → K))) ∧
      letI : MulAction G Omega := MulAction.compHom Omega rho
      B = MulAction.stabilizer G b ∧ TwoRankAtLeastTwo G ∧ fusionStronglyEmbedded B ∧
      MulAction.IsMultiplyPretransitive G Omega 2 ∧
      Nat.card {x : G // x ∈ B ∧ IsInvolution x} = 2 ^ (2 * m + 1) - 1 ∧
      ∃ (a0 b0 : Omega) (w : G) (T0 : Subgroup G),
        a0 ≠ b0 ∧ w • a0 = b0 ∧ w • b0 = a0 ∧
        (T0 : Set G) = {x | x • a0 = a0 ∧ x • b0 = b0} ∧
        IsCyclic T0 ∧ Nat.card T0 = 2 ^ (2 * m + 1) - 1 ∧
        ∀ x ∈ T0, rightConjugateElem x w = x⁻¹ := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  let pinf : ℙ K (Fin 4 → K) := Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
  let G := SuzukiMatrixGroup m
  obtain ⟨rho, b, S, hrho, hproperties⟩ := suzuki_natural_action_standard_pair m hm
  refine ⟨rho, b, (MulAction.stabilizer (Equiv.Perm Omega) b).comap rho, hrho, ?_⟩
  let : MulAction G Omega := MulAction.compHom Omega rho
  obtain ⟨hN, htwo, hpair⟩ := hproperties
  have hB : (MulAction.stabilizer (Equiv.Perm Omega) b).comap rho =
      MulAction.stabilizer G b := by
    ext g
    rfl
  have hdata := bender_suzukiMatrixGroup_borel m (by omega) S
  have hZcard : Nat.card (Subgroup.center (S : Subgroup G)) = 2 ^ (2 * m + 1) :=
    hdata.2.2.2.1
  have hrank : TwoRankAtLeastTwo G := rank_two_of_sylow_center S (by
    rw [hZcard]
    simpa only [show 2 ^ 2 = 4 from rfl] using
      Nat.pow_le_pow_right (n := 2) (i := 2) (j := 2 * m + 1) (by omega) (by omega)) hdata.2.2.1
  have hSE : fusionStronglyEmbedded (MulAction.stabilizer G b) := by
    rw [← hN]
    exact hdata.1
  have hcount : Nat.card {x : G // x ∈ MulAction.stabilizer G b ∧ IsInvolution x} =
      2 ^ (2 * m + 1) - 1 := by
    rw [point_involution_card_of_sylow_center S b hN
      (suzuki_sylow_involutions_mem_center m hm S) hdata.2.2.1, hZcard]
  exact ⟨hB, hrank, hB.symm ▸ hSE, htwo, hB.symm ▸ hcount, hpair⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
