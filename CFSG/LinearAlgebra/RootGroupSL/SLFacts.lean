module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferLevi

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

variable {k X : Type} [Field k] [AddCommGroup X] [Module k X]

theorem pCore_two_specialLinearGroup_eq_bot' [Finite k] [CharP k 2] [Module.Finite k X] :
    CFSG.pCore 2 (SpecialLinearGroup k X) = ⊥ := by
  let b := Module.finBasis k X
  let e := Matrix.SpecialLinearGroup.toLin_equiv b
  have h := CFSG.pCore_map_iso 2 e
  have hbot : CFSG.pCore 2
      (Matrix.SpecialLinearGroup (Fin (Module.finrank k X)) k) = ⊥ :=
    pCore_two_specialLinearGroup_eq_bot_of_charTwo (K := k) (Module.finrank k X)
  rw [hbot, Subgroup.map_bot] at h
  exact h.symm

theorem exists_smul_of_commute_specialLinearGroup [Finite k] [Module.Finite k X]
    (u : X ≃ₗ[k] X)
    (hu : ∀ s : SpecialLinearGroup k X, u * SpecialLinearGroup.toLinearEquiv s =
      SpecialLinearGroup.toLinearEquiv s * u) :
    ∃ c : kˣ, ∀ x : X, u x = (c : k) • x := by
  classical
  let b := Module.finBasis k X
  let M := LinearMap.toMatrix b b (u : X →ₗ[k] X)
  have hMem : M ∈ Set.range (Matrix.scalar (Fin (Module.finrank k X))) := by
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    let A : Matrix (Fin (Module.finrank k X)) (Fin (Module.finrank k X)) k := t.toMatrix
    have hdetA : A.det = 1 := t.det
    let gt : Matrix.SpecialLinearGroup (Fin (Module.finrank k X)) k := ⟨A, hdetA⟩
    let sv : SpecialLinearGroup k X := Matrix.SpecialLinearGroup.toLin_equiv b gt
    have hsv : (sv : X →ₗ[k] X) = Matrix.toLin b b A := by
      simpa [sv, gt, A] using Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq b gt
    have hAmat : LinearMap.toMatrix b b (sv : X →ₗ[k] X) = A := by
      rw [hsv, LinearMap.toMatrix_toLin]
    have hcomm := hu sv
    have hcomm_lin : (u : X →ₗ[k] X) * (sv : X →ₗ[k] X) =
        (sv : X →ₗ[k] X) * (u : X →ₗ[k] X) := by
      have h := congrArg (fun e : X ≃ₗ[k] X => (e : X →ₗ[k] X)) hcomm
      simpa [LinearEquiv.coe_toLinearMap_mul] using h
    have hmat : M * A = A * M := by
      have h := congrArg (LinearMap.toMatrix b b) hcomm_lin
      simpa [M, hAmat, LinearMap.toMatrix_mul] using h
    rw [commute_iff_eq]
    simpa [A] using hmat.symm
  obtain ⟨c, hc⟩ := hMem
  have hlin : (u : X →ₗ[k] X) = c • (LinearMap.id : X →ₗ[k] X) := by
    calc (u : X →ₗ[k] X)
      = Matrix.toLin b b (LinearMap.toMatrix b b (u : X →ₗ[k] X)) := by
          rw [Matrix.toLin_toMatrix]
      _ = Matrix.toLin b b M := rfl
      _ = Matrix.toLin b b (Matrix.scalar (Fin (Module.finrank k X)) c) := by rw [hc]
      _ = c • (LinearMap.id : X →ₗ[k] X) := Matrix.toLin_scalar b c
  by_cases hX : Subsingleton X
  · haveI : Subsingleton X := hX
    exact ⟨1, fun x => Subsingleton.elim _ _⟩
  · haveI : Nontrivial X := not_subsingleton_iff_nontrivial.mp hX
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    have hc0 : c ≠ 0 := by
      intro h0
      have hzero : (u : X →ₗ[k] X) = 0 := by rw [hlin, h0, zero_smul]
      have hux0 : u x = 0 := by
        have := congrArg (fun f : X →ₗ[k] X => f x) hzero
        simpa using this
      have hu0 : u 0 = 0 := map_zero u
      exact hx (u.injective (hux0.trans hu0.symm))
    refine ⟨Units.mk0 c hc0, fun x => ?_⟩
    have hx' := congrArg (fun f : X →ₗ[k] X => f x) hlin
    simpa using hx'

end CFSG.LinearAlgebra.RootGroupSL
