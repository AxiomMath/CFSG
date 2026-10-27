module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.BlockE7
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairE8Central
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairE8Theta
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.ClassicalInvolution.ModelFacts (E7sc stdRankOne)
open CFSG.ClassicalInvolution.ModelFacts.Levi (thetaE8)


theorem unit_mul_self_gf3 (u : (GaloisField 3 1)ˣ) : u * u = 1 := by
  have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 3 1) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact Q3.Q3W.card_gf3
  have h1 : (u : GaloisField 3 1) ^ (Fintype.card (GaloisField 3 1) - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ u.ne_zero
  rw [hF] at h1
  exact Units.ext (by simpa [sq] using h1)

theorem hasCleanFullClassBMember_of_lieModel_e8
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q] (h : CFSG.Blueprint.LieModel Q .E8 0 3 1) :
    HasCleanFullClassBMember Q := by
  have _hGA := hGA
  have hadm : StatedLieAdmissible .E8 0 3 1 := h.admissible
  obtain ⟨α, hαs, hαk⟩ : ∃ α : ↥(adjointGroup .E8 (GaloisField 3 1)) →* Q,
      Function.Surjective α ∧ α.ker ≤ center ↥(adjointGroup .E8 (GaloisField 3 1)) :=
    Upgrade.lieModelCentralCover .E8 0 3 1 Nat.prime_three (by norm_num) trivial hadm Q h
  obtain ⟨Θ, hΘk, hΘr, hΘc⟩ := exists_thetaE8 hadm
  have hX : BlockData (E7sc 3 1) := blockData_e7sc
  haveI : Finite (E7sc 3 1) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := GaloisField 3 1)
      CFSG.LieType.Steinberg.Minuscule.e7Data_valid
  haveI : Group.IsPerfect (E7sc 3 1) := hX.quasisimple.1
  have hperf : commutator (E7sc 3 1) = ⊤ := by simp
  have hZ2 : Nat.card ↥(center (E7sc 3 1)) = 2 :=
    ComponentClassification.HarrisLit.T1.P54.E7Row.card_center_E7sc (p := 3) (f := 1)
      (by norm_num) one_ne_zero
  have hF2 : ringChar (GaloisField 3 1) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 1) 3]
    norm_num
  have hdL : dTheta (GaloisField 3 1) ∈ layerE7 (GaloisField 3 1) :=
    centralizer_stdRankOne_le_layer hF2 unit_mul_self_gf3 hΘc (c := dTheta (GaloisField 3 1))
      fun r hr => dTheta_comm hr
  rw [← hΘr] at hdL
  obtain ⟨w, hw⟩ := hdL
  have hwc : w ∈ center (E7sc 3 1) :=
    mem_center_of_commute_map Θ hΘk hperf fun y => by
      rw [hw]
      exact (hΘc (Θ y) (hΘr ▸ ⟨y, rfl⟩) _ dTheta_mem).symm
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [map_one] at hw
    exact dTheta_ne_one hF2 hw.symm
  have hw2 : orderOf w = 2 := by
    have hd : orderOf w ∣ 2 := hZ2 ▸ Subgroup.orderOf_dvd_natCard _ hwc
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.1 h1) hw1
    · exact h2
  have hΘinj : Function.Injective Θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxc : x ∈ center (E7sc 3 1) := hΘk hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (⟨1, one_mem _⟩ : ↥(center (E7sc 3 1)))).1 hZ2
    have hxy : (⟨x, hxc⟩ : ↥(center (E7sc 3 1))) = y :=
      hy _ (fun h' => hx1 (congrArg Subtype.val h'))
    have hwy : (⟨w, hwc⟩ : ↥(center (E7sc 3 1))) = y :=
      hy _ (fun h' => hw1 (congrArg Subtype.val h'))
    have hxw : x = w := congrArg Subtype.val (hxy.trans hwy.symm)
    rw [hxw, MonoidHom.mem_ker, hw] at hx
    exact dTheta_ne_one hF2 hx
  have hZ : center ↥(adjointGroup .E8 (GaloisField 3 1)) = ⊥ := center_adjointGroup_eq_bot
  have hαinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hαk.trans hZ.le
  have hnorm : (Θ.range.subgroupOf
      (centralizer ({Θ w} : Set ↥(adjointGroup .E8 (GaloisField 3 1))))).Normal := by
    rw [hw, hΘr]
    exact normal_layerE7_centralizer_dTheta hF2 unit_mul_self_gf3 hΘc
  exact hasCleanFullClassBMember_of_block α hαs hαk Θ (hαinj.comp hΘinj) hw2 hwc hnorm hX

end CFSG.OddStandard.HigherRank.F3
