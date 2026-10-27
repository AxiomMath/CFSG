module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Matrix LinearAlgebra.Projectivization

theorem psl2_model_action_point_and_pair (f : ℕ) (hf : 2 ≤ f) :
    let K := BinaryGaloisField f
    let Omega := ℙ K (Fin 2 → K)
    let G := PSL2BinaryMatrixGroup f
    let H := Matrix.ProjGenLinGroup (Fin 2) K
    ∃ (e : G ≃* H) (rhoH : H →* Equiv.Perm Omega) (rho : G →* Equiv.Perm Omega)
        (b : Omega) (B : Subgroup G),
      rho = rhoH.comp e.toMonoidHom ∧
      (∀ (g : G) (z : Omega) (A : GL (Fin 2) K),
        Matrix.ProjGenLinGroup.mk A = e g →
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
  let G := PSL2BinaryMatrixGroup f
  let H := Matrix.ProjGenLinGroup (Fin 2) K
  classical
  let : Fintype K := Fintype.ofFinite K
  let : Finite H := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨e⟩ := psl_charTwo_equiv_pgl f (by omega)
  let : Finite G := Finite.of_injective e e.injective
  obtain ⟨rhoH, b, B, hrhoH, hdata⟩ := linear_model_action_point_and_pair f hf
  refine ⟨e, rhoH, rhoH.comp e.toMonoidHom, b, B.comap e.toMonoidHom, rfl, ?_, ?_⟩
  · intro g z A hA
    exact hrhoH (e g) z A hA
  · exact full_model_point_pair_compHom e rhoH b B (2 ^ f) hdata

theorem sz_model_action_point_and_pair (m : ℕ) (hm : 1 ≤ m) :
    let K := BinaryGaloisField (2 * m + 1)
    let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
    let pinf : ℙ K (Fin 4 → K) := Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
    let G := Sz m
    let H := SuzukiMatrixGroup m
    ∃ (rhoH : H →* Equiv.Perm Omega) (rho : G →* Equiv.Perm Omega)
        (b : Omega) (B : Subgroup G),
      rho = rhoH.comp (suzukiCoverNativeEquiv m).toMonoidHom ∧
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
  let e := suzukiCoverNativeEquiv m
  obtain ⟨rhoH, b, B, hrhoH, hdata⟩ := suzuki_model_action_point_and_pair m hm
  refine ⟨rhoH, rhoH.comp e.toMonoidHom, b, B.comap e.toMonoidHom, rfl, ?_, ?_⟩
  · intro g z
    exact hrhoH (e g) z
  · exact full_model_point_pair_compHom e rhoH b B (2 ^ (2 * m + 1)) hdata

end CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
