module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFU3Aut

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.U3

open CFSG CFSG.Blueprint CFSG.ClassicalInvolution.Q3.Q3PP CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

section Model


theorem outerFixedOddFree_psu3 : OuterFixedOddFree .PSU 3 := by
  intro S _ _ _ hS σ hσ hout
  have hFT : IsFundTag StatedLieTag.PSU := trivial
  have hadm : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover _ 3 3 1 Nat.prime_three (by norm_num) hFT hadm S hS
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := center_eq_bot_of_isQuasisimple hSq
  have : Group.IsPerfect (modelUniv .PSU 3 3 1 Nat.prime_three).K :=
    ⟨((ModelFacts.modelClauseZero .PSU 3 3 1 Nat.prime_three hFT hadm).1).1⟩
  obtain ⟨e₀, -⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  let E : (modelUniv .PSU 3 3 1 Nat.prime_three).K ⧸
      Subgroup.center (modelUniv .PSU 3 3 1 Nat.prime_three).K ≃*
      Su F9 3 1 3 ⧸ Subgroup.center (Su F9 3 1 3) :=
    QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  let e : S ≃* Su F9 3 1 3 ⧸ Subgroup.center (Su F9 3 1 3) :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (Q3NM.centralQuotientIso ψ hψ hker).symm).trans E
  have hρ2 : MulAut.congr e σ * MulAut.congr e σ = 1 := by rw [← map_mul, hσ, map_one]
  have hρout : MulAut.congr e σ ∉ innSubgroup (Su F9 3 1 3 ⧸ Subgroup.center (Su F9 3 1 3)) := by
    rintro ⟨y, hy⟩
    apply hout
    refine ⟨e.symm y, MulEquiv.ext fun x => ?_⟩
    have h1 := congrArg (fun φ => φ (e x)) hy
    simp only [MulAut.conj_apply, MulAut.congr_apply] at h1
    rw [MulAut.conj_apply]
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]
    simp
  have h1 := Q3NM.oddCoreIn_fixed_congr_eq_bot' e.symm (MulAut.congr e σ)
    (oddCoreIn_fixed_su3_of_outer _ hρ2 hρout)
  have h2 : MulAut.congr e.symm (MulAut.congr e σ) = σ := by
    ext x
    simp [MulAut.congr_apply]
  rwa [h2] at h1

end Model

end CFSG.ClassicalInvolution.Q3.TL4.U3
