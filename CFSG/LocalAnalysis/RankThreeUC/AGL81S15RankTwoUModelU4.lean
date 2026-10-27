module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUDefs
public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUNormalForm
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUTorusPow
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem hasScalarTorus_hypSU_two_zero {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ 2 ^ f - 1) :
    HasScalarTorus (hypSU h 2 0) q (hypUnitriangular h 2 0) := by
  obtain ⟨A, hAT, hAel, hAc⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s218_u4_model_elemAbelian h hq hdvd
  refine ⟨A, isScalarTorus_of_fieldBorelData
    (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s218_u4_fieldBorelData_model h)
    hAT hAel hAc ?_⟩
  intro σ hσ hσ2 x hx
  obtain ⟨τ, rfl⟩ := hσ
  have hfield : CFSG.Quasithin.H13.Sec53F.Unit.fieldAut h (r := 2) (ε := 0) (τ * τ) = 1 := by
    have h2 : CFSG.Quasithin.H13.Sec53F.Unit.fieldAutHom h 2 0 (τ * τ) = 1 := by
      rw [map_mul]
      exact hσ2
    exact h2
  have hinv : ∀ a : K, τ (τ a) = a := by
    have heq : τ * τ = 1 :=
      CFSG.Quasithin.H13.Sec53F.Unit.eq_one_of_fixes_torus h (ε := 0) (by norm_num)
        (τ * τ) (fun g _ => by rw [hfield]; rfl)
    intro a
    have := congrArg (fun e : K ≃+* K => e a) heq
    simpa using this
  have hxpow : x ^ (2 ^ f - 1) = 1 := by
    obtain ⟨m, hm⟩ := hdvd
    rw [hm, pow_mul, hAel.2 x hx, one_pow]
  exact fieldAut_hypTorus_eq_self_of_involutive h τ hinv (hAT hx) hxpow

end CFSG.LocalAnalysis.RankThreeUC.S15

end
