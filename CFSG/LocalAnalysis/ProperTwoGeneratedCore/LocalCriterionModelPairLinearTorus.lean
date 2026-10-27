module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearTorus

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Matrix LinearAlgebra.Projectivization

theorem linear_natural_action_standard_pair (f : ℕ) (hf : 2 ≤ f) :
    let K := BinaryGaloisField f
    let Omega := ℙ K (Fin 2 → K)
    let G := Matrix.ProjGenLinGroup (Fin 2) K
    ∃ (rho : G →* Equiv.Perm Omega) (b : Omega) (S : Sylow 2 G),
      (∀ (g : G) (z : Omega) (A : GL (Fin 2) K),
        Matrix.ProjGenLinGroup.mk A = g →
          rho g z = (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z) ∧
      letI : MulAction G Omega := MulAction.compHom Omega rho
      Subgroup.normalizer ((S : Subgroup G) : Set G) = MulAction.stabilizer G b ∧
      MulAction.IsMultiplyPretransitive G Omega 2 ∧
      ∃ (a0 b0 : Omega) (w : G) (T0 : Subgroup G),
        a0 ≠ b0 ∧ w • a0 = b0 ∧ w • b0 = a0 ∧
        (T0 : Set G) = {x | x • a0 = a0 ∧ x • b0 = b0} ∧
        IsCyclic T0 ∧ Nat.card T0 = 2 ^ f - 1 ∧
        ∀ x ∈ T0, rightConjugateElem x w = x⁻¹ := by
  let K := BinaryGaloisField f
  let Omega := ℙ K (Fin 2 → K)
  let G := Matrix.ProjGenLinGroup (Fin 2) K
  obtain ⟨rho, b, S, hrho, hN, _hregular, htwoRaw⟩ :=
    pgl_sylow_normalizer_action f hf
  refine ⟨rho, b, S, hrho, ?_⟩
  let : MulAction G Omega := MulAction.compHom Omega rho
  have hN' : Subgroup.normalizer ((S : Subgroup G) : Set G) =
      MulAction.stabilizer G b := by
    rw [hN]
    ext g
    rfl
  have htwo : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    exact htwoRaw a b c d hab hcd
  obtain ⟨a0, b0, w, T0, hab, hwa, hwb, hTset, hTcyclic, hTcard, hinvert⟩ :=
    pgl_standard_pair_torus (K := K) hrho
  refine ⟨hN', htwo, a0, b0, w, T0, hab, hwa, hwb, hTset, hTcyclic, ?_, hinvert⟩
  calc
    Nat.card T0 = Nat.card K - 1 := hTcard
    _ = 2 ^ f - 1 := by
      rw [show Nat.card K = 2 ^ f from GaloisField.card 2 f (by omega)]

end CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
