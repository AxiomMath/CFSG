module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionProductFactors
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolutionProduct

variable {X Y : Type*} [Group X] [Group Y]

theorem perfect_normal_image_eq_bot_or_eq
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A B : Subgroup G) (hAB : A ≤ B)
    (hA : (A.subgroupOf B).Normal) [Group.IsPerfect A]
    (hB : CFSG.Open.IsQuasisimple (B.map f)) :
    A.map f = ⊥ ∨ A.map f = B.map f := by
  let I := (A.map f).subgroupOf (B.map f)
  let : I.Normal := normal_subgroupOf_image f A B hAB hA
  let : Group.IsPerfect (A.map f) :=
    Group.IsPerfect.ofSurjective (f.subgroupMap_surjective A)
  let e : I ≃* A.map f := Subgroup.subgroupOfEquivOfLe (Subgroup.map_mono hAB)
  let : Group.IsPerfect I :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rcases Quasisimple.perfect_subnormal_eq_bot_or_eq_top hB I
      (Components.chain_of_mathlib_subnormal (inferInstance : I.Normal).isSubnormal) with
      hbot | htop
  · left
    have h := congrArg (Subgroup.map (B.map f).subtype) hbot
    simpa only [I, Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_mono hAB),
      Subgroup.map_bot] using h
  · right
    exact le_antisymm (Subgroup.map_mono hAB) (Subgroup.subgroupOf_eq_top.mp htop)

theorem pComponent_eq_left_or_right_factor (p : ℕ) (L : Subgroup (X × Y))
    (hL : CFSG.IsPComponent p L) :
    L = (L.map (MonoidHom.fst X Y)).prod (⊥ : Subgroup Y) ∨
      L = (⊥ : Subgroup X).prod (L.map (MonoidHom.snd X Y)) := by
  let : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
  obtain ⟨hchain, hcomponent, hminimal⟩ :=
    (CatalogueBAlternating.pComponent_iff_minimal_image p L).mp hL
  have hsub := hL.choose_spec.2.1
  let A := (L.map (MonoidHom.fst X Y)).prod (⊥ : Subgroup Y)
  let B := (⊥ : Subgroup X).prod (L.map (MonoidHom.snd X Y))
  have hAeq : A = L ⊓ (MonoidHom.snd X Y).ker := leftFactor_eq_inf_kernel L hsub
  have hBeq : B = L ⊓ (MonoidHom.fst X Y).ker := rightFactor_eq_inf_kernel L hsub
  have hAL : A ≤ L := hAeq.le.trans inf_le_left
  have hBL : B ≤ L := hBeq.le.trans inf_le_left
  have hAsub : A.IsSubnormal := by
    rw [hAeq]
    exact hsub.inf (inferInstance : (MonoidHom.snd X Y).ker.Normal).isSubnormal
  have hBsub : B.IsSubnormal := by
    rw [hBeq]
    exact hsub.inf (inferInstance : (MonoidHom.fst X Y).ker.Normal).isSubnormal
  have hAN : (A.subgroupOf L).Normal := by
    rw [hAeq, Subgroup.inf_subgroupOf_left]
    infer_instance
  have hBN : (B.subgroupOf L).Normal := by
    rw [hBeq, Subgroup.inf_subgroupOf_left]
    infer_instance
  let : Group.IsPerfect (L.map (MonoidHom.fst X Y)) := fst_image_perfect L
  let : Group.IsPerfect (L.map (MonoidHom.snd X Y)) := snd_image_perfect L
  let eA : A ≃* L.map (MonoidHom.fst X Y) := leftFactorEquiv _
  let eB : B ≃* L.map (MonoidHom.snd X Y) := rightFactorEquiv _
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := eA.symm.toMonoidHom) eA.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := eB.symm.toMonoidHom) eB.symm.surjective
  let q := QuotientGroup.mk' (CFSG.pPrimeCore p (X × Y))
  have hjoin : L = A ⊔ B :=
    (perfect_subnormal_eq_product L hsub).trans (product_eq_sup_factors _ _)
  rcases perfect_normal_image_eq_bot_or_eq q A L hAL hAN hcomponent.2.2 with hAbot | hAfull
  · right
    have hBfull : B.map q = L.map q := by
      conv_rhs => rw [hjoin, Subgroup.map_sup, hAbot, bot_sup_eq]
    exact (hminimal B hBL (Components.chain_of_mathlib_subnormal hBsub) hBfull).symm
  · left
    exact (hminimal A hAL (Components.chain_of_mathlib_subnormal hAsub) hAfull).symm

end CFSG.ComponentClassification.CatalogueBProjectiveInvolutionProduct
