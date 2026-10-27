module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairCanonical
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84TorusModels

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open Matrix
open scoped LinearAlgebra.Projectivization

theorem linear_field_model_action_point_and_pair
    {K : Type} [Field K] [Finite K] (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f) :
    let F := BinaryGaloisField f
    let Omega := ℙ F (Fin 2 → F)
    let G := GLAProj (GLASLGroup (Fin 2) K)
    let H := ProjGenLinGroup (Fin 2) F
    ∃ (ePSL : PSL2BinaryMatrixGroup f ≃* H)
        (rhoH : H →* Equiv.Perm Omega) (rho : G →* Equiv.Perm Omega)
        (b : Omega) (B : Subgroup G),
      rho = rhoH.comp ((glaSL2EquivNative f hf hcard).trans ePSL).toMonoidHom ∧
      (∀ (g : G) (z : Omega) (A : GL (Fin 2) F),
        ProjGenLinGroup.mk A = ePSL (glaSL2EquivNative f hf hcard g) →
          rho g z = (GeneralLinearGroup.toLin A).toLinearEquiv • z) ∧
      letI : MulAction G Omega := MulAction.compHom Omega rho
      B = MulAction.stabilizer G b ∧ TwoRankAtLeastTwo G ∧ fusionStronglyEmbedded B ∧
      MulAction.IsMultiplyPretransitive G Omega 2 ∧
      Nat.card {x : G // x ∈ B ∧ IsInvolution x} = 2 ^ f - 1 ∧
      ∃ (a0 b0 : Omega) (w : G) (T0 : Subgroup G),
        a0 ≠ b0 ∧ w • a0 = b0 ∧ w • b0 = a0 ∧
        (T0 : Set G) = {x | x • a0 = a0 ∧ x • b0 = b0} ∧
        IsCyclic T0 ∧ Nat.card T0 = 2 ^ f - 1 ∧
        ∀ x ∈ T0, rightConjugateElem x w = x⁻¹ := by
  let F := BinaryGaloisField f
  let Omega := ℙ F (Fin 2 → F)
  let G := GLAProj (GLASLGroup (Fin 2) K)
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Finite (ProjGenLinGroup (Fin 2) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  obtain ⟨ePSL, rhoH, rhoPSL, b, B, hcomp, hrhoPSL, hdata⟩ :=
    psl2_model_action_point_and_pair f hf
  let e := glaSL2EquivNative f hf hcard
  let : Finite (PSL2BinaryMatrixGroup f) := Finite.of_injective ePSL ePSL.injective
  refine ⟨ePSL, rhoH, rhoPSL.comp e.toMonoidHom, b, B.comap e.toMonoidHom, ?_, ?_, ?_⟩
  · rw [hcomp]
    rfl
  · intro g z A hA
    exact hrhoPSL (e g) z A hA
  · exact full_model_point_pair_compHom e rhoPSL b B (2 ^ f) hdata

theorem suzuki_field_model_action_point_and_pair
    {K : Type} [Field K] [Finite K] (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card K = 2 ^ (2 * m + 1)) :
    let F := BinaryGaloisField (2 * m + 1)
    let pi : F ≃+* F := iterateFrobeniusEquiv F 2 (m + 1)
    let pinf : ℙ F (Fin 4 → F) := Projectivization.mk F ![1, 0, 0, 0] (by simp)
    let p : F → F → ℙ F (Fin 4 → F) := fun x y =>
      Projectivization.mk F ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ F (Fin 4 → F)) := {pinf} ∪ Set.range fun z : F × F => p z.1 z.2
    let Omega := {z : ℙ F (Fin 4 → F) // z ∈ O}
    let G := GLASzGroup m K
    let H := SuzukiMatrixGroup m
    ∃ (rhoH : H →* Equiv.Perm Omega) (rho : G →* Equiv.Perm Omega)
        (b : Omega) (B : Subgroup G),
      rho = rhoH.comp ((glaSzEquivNative m hm hcard).trans
        (suzukiCoverNativeEquiv m)).toMonoidHom ∧
      (∀ (g : G) (z : Omega), ((rho g z : Omega) : ℙ F (Fin 4 → F)) =
        (GeneralLinearGroup.toLin
          ((glaSzEquivNative m hm hcard g : Sz m) : GL (Fin 4) F)).toLinearEquiv •
            (z : ℙ F (Fin 4 → F))) ∧
      letI : MulAction G Omega := MulAction.compHom Omega rho
      B = MulAction.stabilizer G b ∧ TwoRankAtLeastTwo G ∧ fusionStronglyEmbedded B ∧
      MulAction.IsMultiplyPretransitive G Omega 2 ∧
      Nat.card {x : G // x ∈ B ∧ IsInvolution x} = 2 ^ (2 * m + 1) - 1 ∧
      ∃ (a0 b0 : Omega) (w : G) (T0 : Subgroup G),
        a0 ≠ b0 ∧ w • a0 = b0 ∧ w • b0 = a0 ∧
        (T0 : Set G) = {x | x • a0 = a0 ∧ x • b0 = b0} ∧
        IsCyclic T0 ∧ Nat.card T0 = 2 ^ (2 * m + 1) - 1 ∧
        ∀ x ∈ T0, rightConjugateElem x w = x⁻¹ := by
  let F := BinaryGaloisField (2 * m + 1)
  let pi : F ≃+* F := iterateFrobeniusEquiv F 2 (m + 1)
  let pinf : ℙ F (Fin 4 → F) := Projectivization.mk F ![1, 0, 0, 0] (by simp)
  let p : F → F → ℙ F (Fin 4 → F) := fun x y =>
    Projectivization.mk F ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ F (Fin 4 → F)) := {pinf} ∪ Set.range fun z : F × F => p z.1 z.2
  let Omega := {z : ℙ F (Fin 4 → F) // z ∈ O}
  let e := glaSzEquivNative m hm hcard
  obtain ⟨rhoH, rhoSz, b, B, hcomp, hrhoSz, hdata⟩ := sz_model_action_point_and_pair m hm
  refine ⟨rhoH, rhoSz.comp e.toMonoidHom, b, B.comap e.toMonoidHom, ?_, ?_, ?_⟩
  · rw [hcomp]
    rfl
  · intro g z
    exact hrhoSz (e g) z
  · exact full_model_point_pair_compHom e rhoSz b B (2 ^ (2 * m + 1)) hdata

end CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
