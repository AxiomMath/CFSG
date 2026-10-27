module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUNormalForm
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUTorusPow
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem hasScalarTorus_hypPSU_two_one {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ 2 ^ f - 1) :
    HasScalarTorus (hypPSU h 2 1) q (hypProjUnitriangular h 2 1) := by
  have hK : q ∣ 2 ^ (2 * f) - 1 :=
    hdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨2, by ring⟩)
  have hcop : Nat.Coprime q (Nat.gcd 5 (2 ^ f + 1)) := by
    refine (Nat.Prime.coprime_iff_not_dvd hq).mpr fun hdiv => ?_
    have hq21 : q ∣ 2 ^ f + 1 := hdiv.trans (Nat.gcd_dvd_right 5 (2 ^ f + 1))
    have hq2dvd : q ∣ 2 := by
      have hf1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have hsub := Nat.dvd_sub hq21 hdvd
      rwa [show 2 ^ f + 1 - (2 ^ f - 1) = 2 by omega] at hsub
    have hq_le : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2dvd
    exact hq2 (le_antisymm hq_le hq.two_le)
  obtain ⟨A, hAH, hA, hcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s218_u5_model_elemAbelian h hq hK hcop
  refine ⟨A, isScalarTorus_of_fieldBorelDiagData
    (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s218_u5_fieldBorelDiagData_model h)
    hAH hA hcard ?_⟩
  rintro σ hσ hσ2 x hx
  obtain ⟨τ, rfl⟩ := hσ
  have hτ2 : τ * τ = 1 := by
    refine CFSG.Quasithin.H13.Sec53F.Unit.eq_one_of_fieldP_fixes h (τ * τ) ?_
    intro y _
    rw [map_mul, hσ2]
    rfl
  have hτinv : ∀ a : K, τ (τ a) = a := by
    intro a
    have ha := congrArg (fun e : K ≃+* K => e a) hτ2
    simpa [RingAut.mul_apply] using ha
  have hxq : x ^ (2 ^ f - 1) = 1 := by
    have h1 : orderOf x ∣ q := orderOf_dvd_iff_pow_eq_one.mpr (hA.2 x hx)
    exact orderOf_dvd_iff_pow_eq_one.mp (h1.trans hdvd)
  exact fieldP_eq_self_of_involutive h τ hτinv (hAH hx) hxq

end CFSG.LocalAnalysis.RankThreeUC.S15

end
