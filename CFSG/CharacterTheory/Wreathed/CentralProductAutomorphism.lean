module

public import CFSG.CharacterTheory.Wreathed.QuaternionCharacteristic

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

@[expose] def quaternionCycleFun : QuaternionGroup 2 → QuaternionGroup 2
  | .a i => if i = 0 then .a 0 else if i = 1 then .xa 0 else if i = 2 then .a 2 else .xa 2
  | .xa i => if i = 0 then .xa 3 else if i = 1 then .a 3 else if i = 2 then .xa 1 else .a 1

theorem quaternionCycleFun_cube (q : QuaternionGroup 2) :
    quaternionCycleFun (quaternionCycleFun (quaternionCycleFun q)) = q :=
  (show ∀ q : QuaternionGroup 2,
    quaternionCycleFun (quaternionCycleFun (quaternionCycleFun q)) = q by decide) q

@[expose] def quaternionCycle : MulAut (QuaternionGroup 2) where
  toFun := quaternionCycleFun
  invFun := quaternionCycleFun ∘ quaternionCycleFun
  left_inv := quaternionCycleFun_cube
  right_inv := quaternionCycleFun_cube
  map_mul' := by decide

@[simp] theorem quaternionCycle_a_one : quaternionCycle (QuaternionGroup.a 1) = QuaternionGroup.xa 0 :=
  by decide

@[simp] theorem quaternionCycle_xa_zero :
    quaternionCycle (QuaternionGroup.xa 0) = QuaternionGroup.xa 3 := by decide

@[simp] theorem quaternionCycle_a_two : quaternionCycle (QuaternionGroup.a 2) = QuaternionGroup.a 2 :=
  by decide

theorem quaternionCycle_cube (q : QuaternionGroup 2) :
    quaternionCycle (quaternionCycle (quaternionCycle q)) = q := quaternionCycleFun_cube q

@[expose] def centralProductToV (l : ℕ) (hl : 0 < l) :
    Multiplicative (ZMod (4 * l)) × QuaternionGroup 2 →* vSubgroup l :=
  (centralProductProjection l).codRestrict (vSubgroup l) (fun p =>
    centralProductProjection_range l hl ▸ ⟨p, rfl⟩)

theorem centralProductToV_surjective (l : ℕ) (hl : 0 < l) :
    Function.Surjective (centralProductToV l hl) := by
  intro g
  have hg : g.val ∈ (centralProductProjection l).range :=
    (centralProductProjection_range l hl).symm ▸ g.property
  obtain ⟨p, hp⟩ := hg
  exact ⟨p, Subtype.ext hp⟩

@[expose] def centralProductCycle (l : ℕ) :
    MulAut (Multiplicative (ZMod (4 * l)) × QuaternionGroup 2) :=
  (MulEquiv.refl _).prodCongr quaternionCycle

theorem centralProductCycle_fixes_kernel (l : ℕ) (hl : 0 < l)
    (p : Multiplicative (ZMod (4 * l)) × QuaternionGroup 2)
    (hp : p ∈ (centralProductToV l hl).ker) : centralProductCycle l p = p := by
  rcases p with ⟨c, q⟩
  have heq : centralProductProjection l (c, q) = 1 := congrArg Subtype.val hp
  have hqcenter : quaternionEightEmbedding l q ∈ Subgroup.center (Wreath (4 * l)) := by
    have heq' : diagonalHom (4 * l) c * quaternionEightEmbedding l q = 1 := heq
    have hq : quaternionEightEmbedding l q = (diagonalHom (4 * l) c)⁻¹ :=
      eq_inv_of_mul_eq_one_right heq'
    rw [hq]
    apply (Subgroup.center (Wreath (4 * l))).inv_mem
    exact (element_mem_center_iff _ (by omega) _ _ _).mpr ⟨rfl, rfl⟩
  rcases (quaternionEight_mem_center_iff l hl q).mp hqcenter with rfl | rfl
  · apply Prod.ext
    · rfl
    · exact map_one quaternionCycle
  · apply Prod.ext
    · rfl
    · exact quaternionCycle_a_two

theorem centralProductCycle_preserves_kernel (l : ℕ) (hl : 0 < l) :
    (centralProductToV l hl).ker ≤
      ((centralProductToV l hl).comp (centralProductCycle l).toMonoidHom).ker := by
  intro p hp
  change centralProductToV l hl (centralProductCycle l p) = 1
  rw [centralProductCycle_fixes_kernel l hl p hp]
  exact hp

@[expose] def vCycleHom (l : ℕ) (hl : 0 < l) : vSubgroup l →* vSubgroup l :=
  (centralProductToV l hl).liftOfRightInverse
    (Function.surjInv (centralProductToV_surjective l hl))
    (Function.surjInv_eq (centralProductToV_surjective l hl))
    ⟨(centralProductToV l hl).comp (centralProductCycle l).toMonoidHom,
      centralProductCycle_preserves_kernel l hl⟩

theorem vCycleHom_apply (l : ℕ) (hl : 0 < l)
    (p : Multiplicative (ZMod (4 * l)) × QuaternionGroup 2) :
    vCycleHom l hl (centralProductToV l hl p) =
      centralProductToV l hl (centralProductCycle l p) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ p

theorem vCycleHom_cube (l : ℕ) (hl : 0 < l) (g : vSubgroup l) :
    vCycleHom l hl (vCycleHom l hl (vCycleHom l hl g)) = g := by
  obtain ⟨⟨c, q⟩, rfl⟩ := centralProductToV_surjective l hl g
  rw [vCycleHom_apply, vCycleHom_apply, vCycleHom_apply]
  change centralProductToV l hl (c, quaternionCycle (quaternionCycle (quaternionCycle q))) = _
  rw [quaternionCycle_cube]

@[expose] def vCycle (l : ℕ) (hl : 0 < l) : MulAut (vSubgroup l) where
  toFun := vCycleHom l hl
  invFun := vCycleHom l hl ∘ vCycleHom l hl
  left_inv := vCycleHom_cube l hl
  right_inv := vCycleHom_cube l hl
  map_mul' := (vCycleHom l hl).map_mul

theorem vCycle_quaternion (l : ℕ) (hl : 0 < l) (q : QuaternionGroup 2) :
    vCycle l hl (quaternionToV l q) = quaternionToV l (quaternionCycle q) := by
  have hq : centralProductToV l hl (1, q) = quaternionToV l q := by
    apply Subtype.ext
    change diagonalHom (4 * l) 1 * quaternionEightEmbedding l q = quaternionEightEmbedding l q
    rw [map_one, one_mul]
  change vCycleHom l hl (quaternionToV l q) = _
  rw [← hq, vCycleHom_apply]
  apply Subtype.ext
  change diagonalHom (4 * l) 1 * quaternionEightEmbedding l (quaternionCycle q) = _
  rw [map_one, one_mul]
  rfl

theorem vCycle_cube (l : ℕ) (hl : 0 < l) : (vCycle l hl) ^ 3 = 1 := by
  apply MulEquiv.ext
  intro g
  change vCycleHom l hl (vCycleHom l hl (vCycleHom l hl g)) = g
  exact vCycleHom_cube l hl g

theorem vCycle_order (l : ℕ) (hl : 0 < l) : orderOf (vCycle l hl) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [orderOf_eq_prime_iff]
  refine ⟨vCycle_cube l hl, ?_⟩
  intro heq
  have hg := DFunLike.congr_fun heq (quaternionToV l (QuaternionGroup.a 1))
  change vCycle l hl (quaternionToV l (QuaternionGroup.a 1)) =
    quaternionToV l (QuaternionGroup.a 1) at hg
  rw [vCycle_quaternion, quaternionCycle_a_one] at hg
  have hbad := quaternionToV_injective l hl hg
  cases hbad

theorem vCycle_fixes_center (l : ℕ) (hl : 0 < l) (g : vSubgroup l)
    (hg : g ∈ Subgroup.center (vSubgroup l)) : vCycle l hl g = g := by
  have hg' := (v_mem_center_iff l hl g).mp hg
  rw [center_eq_diagonal_range _ (by omega)] at hg'
  obtain ⟨c, hc⟩ := hg'
  have hpre : centralProductToV l hl (c, 1) = g := by
    apply Subtype.ext
    change diagonalHom (4 * l) c * quaternionEightEmbedding l 1 = g.val
    rw [map_one, mul_one, hc]
  change vCycleHom l hl g = g
  rw [← hpre, vCycleHom_apply]
  change centralProductToV l hl (c, quaternionCycle 1) = _
  rw [map_one]

end CFSG.Wreathed
