module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReeF4Core
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6CrossRed
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem fifteen_dvd_reeF4_pow_four_sub_one (m : ℕ) : 15 ∣ (2 ^ (2 * m + 1)) ^ 4 - 1 := by
  have h : (2 ^ (2 * m + 1)) ^ 4 = 16 ^ (2 * m + 1) := by
    rw [pow_right_comm]
    norm_num
  rw [h]
  have h2 := Nat.sub_dvd_pow_sub_pow 16 1 (2 * m + 1)
  rw [one_pow] at h2
  exact (by norm_num : 15 ∣ 16 - 1).trans h2

theorem dvd_reeF4_pow_four_sub_one_of_mem {p : ℕ} (hp : p = 3 ∨ p = 5) (m : ℕ) :
    p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1 := by
  have h15 := fifteen_dvd_reeF4_pow_four_sub_one m
  rcases hp with rfl | rfl
  · exact (by norm_num : 3 ∣ 15).trans h15
  · exact (by norm_num : 5 ∣ 15).trans h15


@[expose] def ReeF4InnerPlaneBalanceLow (p : ℕ) : Prop :=
  ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], 1 ≤ a →
    Nat.card K = 2 ^ (2 * a + 1) → InnerPlaneBalance p (ReeTag.F4.reeGamma K a)

section OuterPlanes


theorem isLocallyBalancedAbs_two_reeGamma_F4_of_inner_odd {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp35 : p = 3 ∨ p = 5)
    (hin : InnerPlaneBalance p (ReeTag.F4.reeGamma K a)) :
    IsLocallyBalancedAbs p 2 (ReeTag.F4.reeGamma K a) := by
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  have : Finite (ReeTag.F4.reeGamma K a) := inferInstance
  have hinj : Function.Injective
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  refine isLocallyBalancedAbs_two_of_planes_and_fields hp hinj hin ?_
  intro D hD _ hDin
  obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
  exact ⟨x, hxD, hxin, fieldCoreAt_reeGamma ha hK hp hp2
    (dvd_reeF4_pow_four_sub_one_of_mem hp35 a) x (hD.2 x hxD) hxin⟩

end OuterPlanes

section Family


theorem localTwoCrossFamCat_reeF4_of_inner (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hin : ReeF4InnerPlaneBalanceLow p) : LocalTwoCrossFamCat p .reeF4 := by
  rintro ⟨d, hv⟩ ⟨m, rfl⟩ _ _
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  obtain ⟨X, _, _, _, hm1, hX, -, ⟨e⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_reeGamma_F4_of_inner_odd hm1 hX hpp hp (hin m X hm1 hX))

end Family

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
