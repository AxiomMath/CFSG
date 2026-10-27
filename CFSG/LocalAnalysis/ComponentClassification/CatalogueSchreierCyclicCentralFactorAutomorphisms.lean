module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.ComponentClassification.CatalogueSchreierCyclicCentralFactor

variable {L Z : Type*} [Group L] [Group Z]

@[expose] def productAutomorphismHom :
    MulAut L × MulAut Z →* MulAut (L × Z) where
  toFun pair := pair.1.prodCongr pair.2
  map_one' := by ext member <;> rfl
  map_mul' _ _ := by ext member <;> rfl

theorem productAutomorphismHom_injective :
    Function.Injective (productAutomorphismHom (L := L) (Z := Z)) := by
  intro first second heq
  apply Prod.ext
  · apply MulEquiv.ext
    intro member
    exact congrArg (fun automorphism : MulAut (L × Z) =>
      (automorphism (member, 1)).1) heq
  · apply MulEquiv.ext
    intro member
    exact congrArg (fun automorphism : MulAut (L × Z) =>
      (automorphism (1, member)).2) heq

theorem automorphism_inl_second [Group.IsPerfect L] [IsMulCommutative Z]
    (automorphism : MulAut (L × Z)) (member : L) :
    (automorphism (member, 1)).2 = 1 := by
  have htrivial := PerfectAutomorphisms.hom_eq_one_of_commutative
    ((MonoidHom.snd L Z).comp
      (automorphism.toMonoidHom.comp (MonoidHom.inl L Z)))
  exact DFunLike.congr_fun htrivial member

theorem automorphism_inr_first [IsMulCommutative Z]
    (hcenter : Subgroup.center L = ⊥)
    (automorphism : MulAut (L × Z)) (member : Z) :
    (automorphism (1, member)).1 = 1 := by
  have hcentral : (1, member) ∈ Subgroup.center (L × Z) := by
    rw [Subgroup.center_prod]
    exact ⟨Subgroup.one_mem _,
      (Subgroup.center_eq_top (G := Z)).symm ▸ Subgroup.mem_top member⟩
  have himage : automorphism (1, member) ∈ Subgroup.center (L × Z) :=
    Subgroup.map_center_le_center automorphism.surjective
      (Subgroup.mem_map_of_mem automorphism.toMonoidHom hcentral)
  rw [Subgroup.center_prod] at himage
  have hfirst := himage.1
  rw [hcenter] at hfirst
  exact Subgroup.mem_bot.mp hfirst

@[expose] def leftRestriction [Group.IsPerfect L] [IsMulCommutative Z]
    (automorphism : MulAut (L × Z)) : MulAut L where
  toFun member := (automorphism (member, 1)).1
  invFun member := (automorphism.symm (member, 1)).1
  left_inv member := by
    have h := congrArg Prod.fst (automorphism.symm_apply_apply (member, 1))
    have hpair : automorphism (member, 1) = ((automorphism (member, 1)).1, 1) :=
      Prod.ext rfl (automorphism_inl_second automorphism member)
    rw [hpair] at h
    exact h
  right_inv member := by
    have h := congrArg Prod.fst (automorphism.apply_symm_apply (member, 1))
    have hpair : automorphism.symm (member, 1) =
        ((automorphism.symm (member, 1)).1, 1) :=
      Prod.ext rfl (automorphism_inl_second automorphism.symm member)
    rw [hpair] at h
    exact h
  map_mul' left right := by
    have h := congrArg Prod.fst (automorphism.map_mul (left, 1) (right, 1))
    simpa only [Prod.mk_mul_mk, mul_one, Prod.fst_mul] using h

@[expose] def rightRestriction [IsMulCommutative Z]
    (hcenter : Subgroup.center L = ⊥)
    (automorphism : MulAut (L × Z)) : MulAut Z where
  toFun member := (automorphism (1, member)).2
  invFun member := (automorphism.symm (1, member)).2
  left_inv member := by
    have h := congrArg Prod.snd (automorphism.symm_apply_apply (1, member))
    have hpair : automorphism (1, member) = (1, (automorphism (1, member)).2) :=
      Prod.ext (automorphism_inr_first hcenter automorphism member) rfl
    rw [hpair] at h
    exact h
  right_inv member := by
    have h := congrArg Prod.snd (automorphism.apply_symm_apply (1, member))
    have hpair : automorphism.symm (1, member) = (1, (automorphism.symm (1, member)).2) :=
      Prod.ext (automorphism_inr_first hcenter automorphism.symm member) rfl
    rw [hpair] at h
    exact h
  map_mul' left right := by
    have h := congrArg Prod.snd (automorphism.map_mul (1, left) (1, right))
    simpa only [Prod.mk_mul_mk, one_mul, Prod.snd_mul] using h

theorem product_restrictions [Group.IsPerfect L] [IsMulCommutative Z]
    (hcenter : Subgroup.center L = ⊥) (automorphism : MulAut (L × Z)) :
    productAutomorphismHom (leftRestriction automorphism,
      rightRestriction hcenter automorphism) = automorphism := by
  apply MulEquiv.ext
  rintro ⟨left, right⟩
  have hleft : automorphism (left, 1) = ((automorphism (left, 1)).1, 1) :=
    Prod.ext rfl (automorphism_inl_second automorphism left)
  have hright : automorphism (1, right) = (1, (automorphism (1, right)).2) :=
    Prod.ext (automorphism_inr_first hcenter automorphism right) rfl
  have hmul := automorphism.map_mul (left, 1) (1, right)
  rw [hleft, hright] at hmul
  change ((automorphism (left, 1)).1, (automorphism (1, right)).2) =
    automorphism (left, right)
  simpa only [Prod.mk_mul_mk, one_mul, mul_one] using hmul.symm

theorem productAutomorphismHom_surjective [Group.IsPerfect L] [IsMulCommutative Z]
    (hcenter : Subgroup.center L = ⊥) :
    Function.Surjective (productAutomorphismHom (L := L) (Z := Z)) :=
  fun automorphism => ⟨(leftRestriction automorphism, rightRestriction hcenter automorphism),
    product_restrictions hcenter automorphism⟩

@[expose] noncomputable def automorphismEquivalence [Group.IsPerfect L] [IsMulCommutative Z]
    (hcenter : Subgroup.center L = ⊥) : MulAut (L × Z) ≃* MulAut L × MulAut Z :=
  (MulEquiv.ofBijective productAutomorphismHom
    ⟨productAutomorphismHom_injective, productAutomorphismHom_surjective hcenter⟩).symm

theorem automorphismEquivalence_apply [Group.IsPerfect L] [IsMulCommutative Z]
    (hcenter : Subgroup.center L = ⊥) (automorphism : MulAut (L × Z)) :
    automorphismEquivalence hcenter automorphism =
      (leftRestriction automorphism, rightRestriction hcenter automorphism) := by
  apply productAutomorphismHom_injective
  exact (MulEquiv.ofBijective_apply_symm_apply productAutomorphismHom _).trans
    (product_restrictions hcenter automorphism).symm

end CFSG.ComponentClassification.CatalogueSchreierCyclicCentralFactor
