module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def centEquiv {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z) (y : Y) :
    ↥(centralizer ({y} : Set Y)) ≃* ↥(centralizer ({e y} : Set Z)) where
  toFun x := ⟨e x, by
    have h := Subgroup.mem_centralizer_singleton_iff.1 x.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h]⟩
  invFun x := ⟨e.symm x, by
    have h := Subgroup.mem_centralizer_singleton_iff.1 x.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h]⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem isSection_of_surjective_hom {B Y : Type*} [Group B] [Group Y] (c : B →* Y)
    (hc : Function.Surjective c) : IsSection Y B :=
  ⟨⊤, c.comp (⊤ : Subgroup B).subtype, fun y => by
    obtain ⟨b, hb⟩ := hc y
    exact ⟨⟨b, trivial⟩, hb⟩⟩

theorem false_of_section_all {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}
    (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hns : ¬ Group.IsSolvable Q) (hQ : ¬ KindFactorAll Kind.ly Q)
    (hsec : ∀ u : ↥J ⧸ center ↥J, orderOf u = 2 →
      IsSection Q ↥(centralizer ({u} : Set (↥J ⧸ center ↥J)))) : False := by
  have hnsY : ¬ Group.IsSolvable (↥J ⧸ center ↥J) := not_isSolvable_quot_of_quasisimple hJ.1
  obtain ⟨ub, hub⟩ := exists_involution_of_not_solvable hnsY
  have hnk : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J) := fun h =>
    hQ (kfa_of_isSection h (IsSection.of_le _ (hsec ub hub)))
  obtain ⟨hZ, -, -⟩ := hfr.reduce hJ hnk
  let e : (↥J ⧸ center ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hu : orderOf (e ub) = 2 := by rw [MulEquiv.orderOf_eq]; exact hub
  have hsecJ : IsSection Q ↥(centralizer ({e ub} : Set ↥J)) :=
    IsSection.of_equiv (centEquiv e ub).symm (hsec ub hub)
  exact hQ (kfa_of_cent_section hfr J (e ub) hu hns hsecJ)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
