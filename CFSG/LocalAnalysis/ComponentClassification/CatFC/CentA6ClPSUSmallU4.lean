module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUSmallBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Tables
public import CFSG.LieType.Multipliers.U43
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem psu_isSimpleGroup_X₀ : IsSimpleGroup CFSG.LieType.Multipliers.U43.X₀ := by
  have h := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU
    CFSG.LieType.Multipliers.U43.F9 3 1
    (by rw [Nat.card_eq_fintype_card, CFSG.LieType.Multipliers.U43.F9.card_eq]; norm_num) 4
    (by norm_num) (by simp)
  rwa [pow_one] at h

theorem psu_small_four_one
    {X : Type} [Group X] [Finite X]
    (hm : LieModel X .PSU 4 3 1) (σ : MulAut X) (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hA : A6Hyp σ D) : A6SmallConcl .PSU 4 1 σ D := by
  obtain ⟨e₀⟩ := CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ hm
  haveI : IsSimpleGroup CFSG.LieType.Multipliers.U43.X₀ := psu_isSimpleGroup_X₀
  haveI : IsSimpleGroup X := e₀.isSimpleGroup
  have hc : Subgroup.center X = ⊥ := psu_center_bot_of_simple_of_nonab hA.psu_not_comm
  haveI : ((MulAut.conj : X →* MulAut X).range).Normal := psu_conj_range_normal
  let θ : (MulAut.conj : X →* MulAut X).range ≃* ↥CFSG.EvenSporadicStandard.M24Std.CU43.P :=
    (MonoidHom.ofInjective (psu_conj_injective hc)).symm.trans
      (e₀.trans CFSG.EvenSporadicStandard.M24Std.CU43.psiEquiv)
  have hC := psu_centralizer_conj_range hc
  have hcard := psu_card_fixed_eq_card_inf hc σ
  have h2 : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
  have h1 : σ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hdvd := hA.dvd
  by_cases hin : σ ∈ (MulAut.conj : X →* MulAut X).range
  · exfalso
    have := CFSG.EvenSporadicStandard.M24Std.CU43.card_inf_centralizer_inner _ θ hC hin h2 h1
    rw [← hcard] at this
    rw [this] at hdvd
    omega
  · refine ⟨fun h => absurd h hin, fun _ hle => ?_⟩
    have := CFSG.EvenSporadicStandard.M24Std.CU43.card_inf_centralizer_outer _ θ hC hin h2
    rw [← hcard] at this
    have h720 : Nat.card ↥(fixedSubgroup σ) = 720 := by
      rcases this with h | h | h | h <;> rw [h] at hdvd hle <;> omega
    exact ⟨h720, Or.inr ⟨rfl, rfl, rfl⟩⟩

end CFSG.ComponentClassification.CatFC
