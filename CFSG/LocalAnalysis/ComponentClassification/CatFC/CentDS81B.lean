module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Basic
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.B.CTIB.UniqueComponentFinal
public import CFSG.Monster.B.CTIB.Rank2158Final
public import CFSG.Monster.B.CTIB.Rank2048
public import CFSG.Monster.Existence.BabyW3Classes
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.CTIB

set_option linter.unusedSectionVars false

theorem dvd_card_of_subgroup {C : Type*} [Group C] (K : Subgroup C) {m : ℕ}
    (h : m ∣ Nat.card K) : m ∣ Nat.card C :=
  h.trans (Subgroup.card_subgroup_dvd_card K)

theorem dvd_card_of_subgroup_quotient_center {C : Type*} [Group C] (K : Subgroup C) {m : ℕ}
    (h : m ∣ Nat.card (K ⧸ center K)) : m ∣ Nat.card C :=
  dvd_card_of_subgroup K (h.trans
    ⟨Nat.card (center K), Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)⟩)


theorem baby_not_isCo2Shape {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.B)
    (τ : X) (hτ : orderOf τ = 2)
    (hab : IsMulCommutative (pCore 2 ↥(centralizer ({τ} : Set X)))) :
    ¬ IsCo2Shape (Nat.card ↥(centralizer ({τ} : Set X))) := by
  intro hshape
  let e' : X ≃* Sbp := e.trans iotaEquiv
  have hs : orderOf (e' τ) = 2 := by rw [MulEquiv.orderOf_eq]; exact hτ
  obtain ⟨i, ⟨hi, hconj⟩, -⟩ := native_four_involution_classes.1 (e' τ) hs
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hconjapp : (MulAut.conj c) (e' τ) = rs i := by rw [MulAut.conj_apply]; exact hc
  have hord : orderOf (rs i) = 2 := by
    rw [← hconjapp, MulEquiv.orderOf_eq]
    exact hs
  have hcard : Nat.card ↥(centralizer ({τ} : Set X)) =
      Nat.card ↥(centralizer ({rs i} : Set Sbp)) := by
    rw [card_centralizer_eq e' τ, card_centralizer_eq (MulAut.conj c) (e' τ), hconjapp]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  ·
    obtain ⟨K, -, -, -, -, -, -, h17⟩ := native_rank_1860_unique_component_final (rs 1) hord
      native_four_involution_classes.2.1
    exact hshape.not_dvd_seventeen
      (hcard ▸ dvd_card_of_subgroup_quotient_center K h17)
  ·
    have hx : c * e' τ * c⁻¹ = xs := hc.trans rs0_eq
    have hQ := qCent_extraspecial hx
    have hnc : ¬ IsMulCommutative (qCent hx) :=
      not_isMulCommutative_of_isExtraspecialPGroup hQ.1 (by rw [hQ.2]; norm_num)
    have h1 : ¬ IsMulCommutative (pCore 2 ↥(centralizer ({e' τ} : Set Sbp))) :=
      not_isMulCommutative_pCore_of_normal (qCent hx) hQ.1.1 hnc
    exact h1 (isMulCommutative_pCore_of_mulEquiv (centEquiv e' τ) hab)
  ·
    obtain ⟨K, -, -, -, -, -, h17⟩ :=
      native_rank_2158_distance_three_product_final.2.1 (rs 5) hord
        native_four_involution_classes.2.2.2.1
    exact hshape.not_dvd_seventeen (hcard ▸ dvd_card_of_subgroup K h17)
  ·
    have h3 : Nat.card ↥(centralizer ({rs 3} : Set Sbp)) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
      have h := Monster.Existence.natCard_centralizer_rep_three
      have h' := @card_centralizer_eq NativeSporadic.B Sbp Units.instGroup _ iotaEquiv
        (iotaEquiv.symm (rs 3))
      rw [MulEquiv.apply_symm_apply] at h'
      rw [← h', h]
      norm_num [CFSG.Monster.GMS.babyCentOrder]
    have hd := hshape.dvd
    rw [hcard, h3] at hd
    revert hd
    norm_num

end CFSG.ComponentClassification.CatFC.DS81
