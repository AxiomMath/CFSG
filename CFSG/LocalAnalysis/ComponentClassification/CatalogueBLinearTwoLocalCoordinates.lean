module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoInvolutionComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBIndexTwoLocal

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoLocal

noncomputable section

open CFSG.GorensteinWalter CatalogueSchreierLinearTwo

universe u

@[expose] def nestedFixedEquiv {A : Type*} [Group A]
    (N H : Subgroup A) (hNH : N ≤ H) (t : H) :
    (Subgroup.centralizer ({t} : Set H)).subgroupOf (N.subgroupOf H) ≃*
      (Subgroup.centralizer ({t.val} : Set A)).subgroupOf N where
  toFun x := ⟨⟨x.val.val.val, x.val.property⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have hx := Subgroup.mem_centralizer_singleton_iff.mp x.property
      exact congrArg Subtype.val hx)⟩
  invFun x := ⟨⟨⟨x.val.val, hNH x.val.property⟩, x.val.property⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp x.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem coordinateG_normal_in_between (K : Type u) [Field K] [Finite K]
    (H : Subgroup (Equiv.Perm (Omega K))) (hGH : coordinateG K ≤ H)
    (hHE : H ≤ coordinateE K) : ((coordinateG K).subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hGH).mpr
    (hHE.trans (coordinateE_le_normalizer_G K))

theorem between_involution_fixed_pComponent (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (hsize : 5 ≤ Nat.card K)
    (H : Subgroup (Equiv.Perm (Omega K))) (hGH : coordinateG K ≤ H)
    (hHE : H ≤ coordinateE K) (t : H) (ht : orderOf t = 2)
    (L : Subgroup ((Subgroup.centralizer ({t} : Set H)).subgroupOf
      ((coordinateG K).subgroupOf H)))
    (hL : CFSG.IsPComponent 2 L) : CFSG.IsQuasisimple L := by
  obtain ⟨p, f, hp, hpodd, hf, hcard⟩ := oddPrimePower_of_odd_card K hodd
  let a : coordinateE K := ⟨t.val, hHE t.property⟩
  have ha : orderOf (a : Equiv.Perm (Omega K)) = 2 :=
    (Subgroup.orderOf_coe t).trans ht
  let e := nestedFixedEquiv (coordinateG K) H hGH t
  have hmap := CatalogueBAlternating.pComponent_map_equiv 2 e L hL
  have hquasi := (CatalogueBLinearTwoInvolution.involution_fixed_pComponent K p f hp hpodd
    hf hcard hsize a ha 2 (L.map e.toMonoidHom) hmap).1
  let r := L.equivMapOfInjective e.toMonoidHom e.injective
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv r
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

theorem between_inner_involution_fixed_solvable (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K))
    (H : Subgroup (Equiv.Perm (Omega K))) (hGH : coordinateG K ≤ H)
    (t : H) (ht : orderOf t = 2) (hinner : t ∈ (coordinateG K).subgroupOf H) :
    Group.IsSolvable ((Subgroup.centralizer ({t} : Set H)).subgroupOf
      ((coordinateG K).subgroupOf H)) := by
  obtain ⟨p, f, hp, hpodd, _hf, hcard⟩ := oddPrimePower_of_odd_card K hodd
  have htD : t.val ∈ coordinateD K := coordinateG_le_D K hinner
  have htambient : orderOf (t.val : Equiv.Perm (Omega K)) = 2 :=
    (Subgroup.orderOf_coe t).trans ht
  let : Group.IsSolvable (CatalogueBLinearTwoInvolution.fixedGroup K t.val) :=
    CatalogueBLinearTwoInvolution.linear_involution_fixedGroup_solvable
      K p f hp hpodd hcard t.val htD htambient
  let e := nestedFixedEquiv (coordinateG K) H hGH t
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem linear_two_index_two_coordinate_local_B (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (hsize : 5 ≤ Nat.card K)
    (H : Subgroup (Equiv.Perm (Omega K))) (hGH : coordinateG K ≤ H)
    (hHE : H ≤ coordinateE K) (hindex : (coordinateG K).relIndex H ≤ 2) :
    Assembly.ComponentType.LocalBProperty H ∧
      ∀ S : Subgroup H, S ≠ ⊥ → IsPGroup 2 S →
        TwoComponents.badSubgroup (Subgroup.normalizer (S : Set H)) = ⊥ := by
  let N := (coordinateG K).subgroupOf H
  let : N.Normal := coordinateG_normal_in_between K H hGH hHE
  apply CatalogueBIndexTwo.localBProperty_and_normalizer_badSubgroup_eq_bot N hindex
  · exact between_inner_involution_fixed_solvable K hodd H hGH
  · intro t ht _htN L hL
    exact between_involution_fixed_pComponent K hodd hsize H hGH hHE t ht L hL

end

end CFSG.ComponentClassification.CatalogueBLinearTwoLocal
