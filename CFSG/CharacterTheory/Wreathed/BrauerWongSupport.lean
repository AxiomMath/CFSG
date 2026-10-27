module

public import CFSG.CharacterTheory.Wreathed.CentralizerFusion

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed

universe u

variable {G : Type u} [Group G]

section Presentation

variable {n : ℕ} {S₁ S₂ T : G}

theorem pow_val_add {m : ℕ} [NeZero m] (x : G) (hx : x ^ m = 1) (a b : ZMod m) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

theorem pow_val_swap_add (x : G) (hx : x ^ 2 = 1) (e : ZMod 2) :
    x ^ (1 + e).val = x * x ^ e.val := by
  rcases swap_exponent_cases e with rfl | rfl
  · rw [add_zero, ZMod.val_zero, pow_zero, mul_one, show (1 : ZMod 2).val = 1 from rfl, pow_one]
  · rw [show (1 + 1 : ZMod 2) = 0 by decide, ZMod.val_zero, pow_zero,
      show (1 : ZMod 2).val = 1 from rfl, pow_one, ← pow_two, hx]

@[expose] def presentationFun (n : ℕ) (S₁ S₂ T : G) (w : Wreath (2 ^ n)) : G :=
  S₁ ^ (coordinateEquiv _ w).1.val * S₂ ^ (coordinateEquiv _ w).2.1.val *
    T ^ (coordinateEquiv _ w).2.2.val

theorem presentationFun_element (n : ℕ) (S₁ S₂ T : G) (a b : ZMod (2 ^ n)) (e : ZMod 2) :
    presentationFun n S₁ S₂ T (element _ a b e) = S₁ ^ a.val * S₂ ^ b.val * T ^ e.val := by
  unfold presentationFun
  rw [show coordinateEquiv (2 ^ n) (element _ a b e) = (a, b, e) from
    (coordinateEquiv (2 ^ n)).apply_symm_apply (a, b, e)]

theorem presentation_swap_left (hT : T ^ 2 = 1) (hconj : T⁻¹ * S₁ * T = S₂) :
    T * S₁ = S₂ * T := by
  have hTinv : T⁻¹ = T := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hT])
  rw [← hconj, hTinv, mul_assoc, mul_assoc, ← pow_two, hT, mul_one]

theorem presentation_swap_right (hT : T ^ 2 = 1) (hconj : T⁻¹ * S₁ * T = S₂) :
    T * S₂ = S₁ * T := by
  have hTinv : T⁻¹ = T := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hT])
  rw [← hconj, hTinv, ← mul_assoc, ← mul_assoc, ← pow_two, hT, one_mul]

theorem presentationFun_mul (hS₁ : S₁ ^ 2 ^ n = 1) (hS₂ : S₂ ^ 2 ^ n = 1) (hT : T ^ 2 = 1)
    (hcomm : S₁ * S₂ = S₂ * S₁) (hconj : T⁻¹ * S₁ * T = S₂) (w w' : Wreath (2 ^ n)) :
    presentationFun n S₁ S₂ T (w * w') =
      presentationFun n S₁ S₂ T w * presentationFun n S₁ S₂ T w' := by
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w
  obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w'
  change presentationFun n S₁ S₂ T (element _ a b e * element _ c d f) =
    presentationFun n S₁ S₂ T (element _ a b e) * presentationFun n S₁ S₂ T (element _ c d f)
  have hpc (i j : ℕ) : Commute (S₁ ^ i) (S₂ ^ j) := (Commute.pow_pow hcomm i j)
  have hTS₁ (i : ℕ) : T * S₁ ^ i = S₂ ^ i * T := by
    induction i with
    | zero => simp
    | succ i ih =>
        rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, presentation_swap_left hT hconj,
          mul_assoc]
  have hTS₂ (i : ℕ) : T * S₂ ^ i = S₁ ^ i * T := by
    induction i with
    | zero => simp
    | succ i ih =>
        rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, presentation_swap_right hT hconj,
          mul_assoc]
  rcases swap_exponent_cases e with rfl | rfl
  · rw [element_base_mul, presentationFun_element, presentationFun_element,
      presentationFun_element, pow_val_add _ hS₁, pow_val_add _ hS₂, ZMod.val_zero, pow_zero,
      mul_one]
    simp only [mul_assoc]
    congr 1
    exact (hpc c.val b.val).left_comm _
  · rw [element_swap_mul, presentationFun_element, presentationFun_element,
      presentationFun_element, pow_val_add _ hS₁, pow_val_add _ hS₂, pow_val_swap_add _ hT,
      show (1 : ZMod 2).val = 1 from rfl, pow_one]
    simp only [mul_assoc]
    congr 1
    rw [show T * (S₁ ^ c.val * (S₂ ^ d.val * T ^ f.val)) =
        S₂ ^ c.val * (S₁ ^ d.val * (T * T ^ f.val)) by
      rw [← mul_assoc, hTS₁, mul_assoc, ← mul_assoc T, hTS₂, mul_assoc]]
    rw [(hpc d.val b.val).left_comm, (hpc d.val c.val).left_comm]

@[expose] def presentationHom (hS₁ : S₁ ^ 2 ^ n = 1) (hS₂ : S₂ ^ 2 ^ n = 1) (hT : T ^ 2 = 1)
    (hcomm : S₁ * S₂ = S₂ * S₁) (hconj : T⁻¹ * S₁ * T = S₂) : Wreath (2 ^ n) →* G where
  toFun := presentationFun n S₁ S₂ T
  map_one' := by
    rw [← element_zero, presentationFun_element, ZMod.val_zero, ZMod.val_zero, pow_zero,
      pow_zero, pow_zero, mul_one, mul_one]
  map_mul' := presentationFun_mul hS₁ hS₂ hT hcomm hconj

variable (hS₁ : S₁ ^ 2 ^ n = 1) (hS₂ : S₂ ^ 2 ^ n = 1) (hT : T ^ 2 = 1)
    (hcomm : S₁ * S₂ = S₂ * S₁) (hconj : T⁻¹ * S₁ * T = S₂)

theorem presentationHom_element (a b : ZMod (2 ^ n)) (e : ZMod 2) :
    presentationHom hS₁ hS₂ hT hcomm hconj (element _ a b e) =
      S₁ ^ a.val * S₂ ^ b.val * T ^ e.val :=
  presentationFun_element n S₁ S₂ T a b e

include hS₁ hS₂ hT hcomm hconj in
theorem presentationHom_s (hn : 1 ≤ n) :
    presentationHom hS₁ hS₂ hT hcomm hconj (Original.s (2 ^ n)) = S₁ := by
  let : Fact (1 < 2 ^ n) := ⟨Nat.one_lt_two_pow (by omega)⟩
  rw [Original.s, presentationHom_element, ZMod.val_one]
  simp

include hS₁ hS₂ hT hcomm hconj in
theorem presentationHom_t (hn : 1 ≤ n) :
    presentationHom hS₁ hS₂ hT hcomm hconj (Original.t (2 ^ n)) = S₂ := by
  let : Fact (1 < 2 ^ n) := ⟨Nat.one_lt_two_pow (by omega)⟩
  rw [Original.t, presentationHom_element, ZMod.val_one]
  simp

include hS₁ hS₂ hT hcomm hconj in
theorem presentationHom_z :
    presentationHom hS₁ hS₂ hT hcomm hconj (Original.z (2 ^ n)) = T := by
  rw [Original.z, presentationHom_element, show (1 : ZMod 2).val = 1 from rfl]
  simp

theorem presentationHom_range (hn : 1 ≤ n) :
    (presentationHom hS₁ hS₂ hT hcomm hconj).range = Subgroup.closure {S₁, S₂, T} := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w
    change presentationHom hS₁ hS₂ hT hcomm hconj (element _ a b e) ∈ _
    rw [presentationHom_element]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_ <;>
      exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact ⟨_, presentationHom_s hS₁ hS₂ hT hcomm hconj hn⟩
    · exact ⟨_, presentationHom_t hS₁ hS₂ hT hcomm hconj hn⟩
    · exact ⟨_, presentationHom_z hS₁ hS₂ hT hcomm hconj⟩

theorem presentationHom_injective [Finite G] (hn : 1 ≤ n) (S : Subgroup G)
    (hgen : Subgroup.closure {S₁, S₂, T} = S) (hcard : Nat.card S = 2 ^ (2 * n + 1)) :
    Function.Injective (presentationHom hS₁ hS₂ hT hcomm hconj) := by
  set f := presentationHom hS₁ hS₂ hT hcomm hconj
  have hrange : f.range = S := (presentationHom_range hS₁ hS₂ hT hcomm hconj hn).trans hgen
  let g : Wreath (2 ^ n) → f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  have hcardeq : Nat.card f.range = Nat.card (Wreath (2 ^ n)) := by
    rw [hrange, hcard, card_wreath, ← pow_mul, pow_succ, mul_comm, mul_comm n 2]
  have hbij : Function.Bijective g := by
    refine ⟨?_, hg⟩
    exact (Function.Surjective.bijective_of_nat_card_le hg hcardeq.ge).1
  intro x y hxy
  apply hbij.1
  exact Subtype.ext hxy

@[expose] def presentationEquiv [Finite G] (hn : 1 ≤ n) (S : Sylow 2 G)
    (hgen : Subgroup.closure {S₁, S₂, T} = (S : Subgroup G))
    (hcard : Nat.card (S : Subgroup G) = 2 ^ (2 * n + 1)) :
    (S : Subgroup G) ≃* Wreath (2 ^ n) :=
  (MulEquiv.ofBijective ((presentationHom hS₁ hS₂ hT hcomm hconj).codRestrict
      (S : Subgroup G) (fun w => by
        rw [← hgen, ← presentationHom_range hS₁ hS₂ hT hcomm hconj hn]
        exact ⟨w, rfl⟩))
    ⟨fun x y hxy => presentationHom_injective hS₁ hS₂ hT hcomm hconj hn _ hgen hcard
        (congrArg Subtype.val hxy),
      fun s => by
        have hs : (s : G) ∈ (presentationHom hS₁ hS₂ hT hcomm hconj).range := by
          rw [presentationHom_range hS₁ hS₂ hT hcomm hconj hn, hgen]
          exact s.property
        obtain ⟨w, hw⟩ := hs
        exact ⟨w, Subtype.ext hw⟩⟩).symm

theorem wreathModelHom_presentationEquiv [Finite G] (hn : 1 ≤ n) (S : Sylow 2 G)
    (hgen : Subgroup.closure {S₁, S₂, T} = (S : Subgroup G))
    (hcard : Nat.card (S : Subgroup G) = 2 ^ (2 * n + 1)) :
    wreathModelHom S (presentationEquiv hS₁ hS₂ hT hcomm hconj hn S hgen hcard) =
      presentationHom hS₁ hS₂ hT hcomm hconj := by
  ext w
  rfl

end Presentation

structure WreathGenerators (n : ℕ) (S : Subgroup G) (S₁ S₂ T : G) : Prop where
  closure_eq : Subgroup.closure {S₁, S₂, T} = S
  card_eq : Nat.card S = 2 ^ (2 * n + 1)
  pow_left : S₁ ^ 2 ^ n = 1
  pow_right : S₂ ^ 2 ^ n = 1
  sq_swap : T ^ 2 = 1
  comm : S₁ * S₂ = S₂ * S₁
  conj : T⁻¹ * S₁ * T = S₂

namespace WreathGenerators

variable {n : ℕ} {S : Sylow 2 G} {S₁ S₂ T : G}
  (hW : WreathGenerators n (S : Subgroup G) S₁ S₂ T)

@[expose] def equiv [Finite G] (hn : 1 ≤ n) : (S : Subgroup G) ≃* Wreath (2 ^ n) :=
  presentationEquiv hW.pow_left hW.pow_right hW.sq_swap hW.comm hW.conj hn S hW.closure_eq
    hW.card_eq

theorem modelHom_eq [Finite G] (hn : 1 ≤ n) :
    wreathModelHom S (hW.equiv hn) =
      presentationHom hW.pow_left hW.pow_right hW.sq_swap hW.comm hW.conj :=
  wreathModelHom_presentationEquiv _ _ _ _ _ hn S _ _

theorem modelHom_s [Finite G] (hn : 1 ≤ n) :
    wreathModelHom S (hW.equiv hn) (Original.s (2 ^ n)) = S₁ := by
  rw [hW.modelHom_eq hn]
  exact presentationHom_s _ _ _ _ _ hn

theorem modelHom_t [Finite G] (hn : 1 ≤ n) :
    wreathModelHom S (hW.equiv hn) (Original.t (2 ^ n)) = S₂ := by
  rw [hW.modelHom_eq hn]
  exact presentationHom_t _ _ _ _ _ hn

theorem modelHom_z [Finite G] (hn : 1 ≤ n) :
    wreathModelHom S (hW.equiv hn) (Original.z (2 ^ n)) = T := by
  rw [hW.modelHom_eq hn]
  exact presentationHom_z _ _ _ _ _

theorem half_eq (hn : 1 ≤ n) : 2 ^ n / 2 = 2 ^ (n - 1) := by
  rw [← twice_half_two_pow n hn, Nat.mul_div_cancel_left _ two_pos]

theorem modelHom_a [Finite G] (hn : 1 ≤ n) :
    wreathModelHom S (hW.equiv hn) (Original.a (2 ^ n)) = S₁ * S₂ := by
  rw [Original.a, map_mul, hW.modelHom_s hn, hW.modelHom_t hn]

theorem modelHom_a_inv [Finite G] (hn : 1 ≤ n) :
    wreathModelHom S (hW.equiv hn) (Original.a (2 ^ n))⁻¹ = S₁⁻¹ * S₂⁻¹ := by
  rw [map_inv, hW.modelHom_a hn, mul_inv_rev]
  exact (show Commute S₁ S₂ from hW.comm).inv_inv.eq.symm

theorem modelHom_x2 [Finite G] (hn : 1 ≤ n) :
    wreathModelHom S (hW.equiv hn) (Original.x2 (2 ^ n)) = S₁ ^ 2 ^ (n - 1) := by
  rw [Original.x2, map_pow, hW.modelHom_s hn, half_eq hn]

theorem modelHom_t_half [Finite G] (hn : 1 ≤ n) :
    wreathModelHom S (hW.equiv hn) (Original.t (2 ^ n) ^ (2 ^ n / 2)) = S₂ ^ 2 ^ (n - 1) := by
  rw [map_pow, hW.modelHom_t hn, half_eq hn]

theorem modelHom_x [Finite G] (hn : 2 ≤ n) :
    wreathModelHom S (hW.equiv (by omega)) (Original.x (2 ^ n)) =
      (S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1) := by
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  have hx2 : Original.x (2 ^ n) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (Original.x (2 ^ n))
    rwa [hstr.involution_orders.1] at h
  have hxinv : (Original.x (2 ^ n))⁻¹ = Original.x (2 ^ n) :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx2)
  rw [← hW.modelHom_a_inv (by omega), ← map_pow, ← half_eq (by omega), inv_pow, ← Original.x,
    hxinv]

theorem modelHom_r [Finite G] (hn : 1 ≤ n) :
    wreathModelHom S (hW.equiv hn) (Original.r (2 ^ n)) = S₁ * S₂⁻¹ := by
  rw [Original.r, map_mul, map_inv, hW.modelHom_s hn, hW.modelHom_t hn]

theorem modelHom_root [Finite G] (hn : 1 ≤ n) :
    wreathModelHom S (hW.equiv hn) (Original.s (2 ^ n) * Original.z (2 ^ n)) = S₁ * T := by
  rw [map_mul, hW.modelHom_s hn, hW.modelHom_z hn]

theorem modelHom_swap_x2 [Finite G] (hn : 1 ≤ n) :
    wreathModelHom S (hW.equiv hn) (Original.z (2 ^ n) * Original.x2 (2 ^ n)) =
      T * S₁ ^ 2 ^ (n - 1) := by
  rw [map_mul, hW.modelHom_z hn, hW.modelHom_x2 hn]

theorem modelHom_element [Finite G] (hn : 1 ≤ n) (a b : ZMod (2 ^ n)) (e : ZMod 2) :
    wreathModelHom S (hW.equiv hn) (element _ a b e) = S₁ ^ a.val * S₂ ^ b.val * T ^ e.val := by
  rw [hW.modelHom_eq hn]
  exact presentationHom_element _ _ _ _ _ a b e

theorem modelBase_eq [Finite G] (hn : 1 ≤ n) :
    modelBase S (hW.equiv hn) = Subgroup.closure {S₁, S₂} := by
  rw [modelBase, ← Original.U_eq, Original.U, MonoidHom.map_closure, Set.image_pair,
    hW.modelHom_s hn, hW.modelHom_t hn]

theorem modelCenter_eq [Finite G] (hn : 1 ≤ n) :
    modelCenter S (hW.equiv hn) = Subgroup.zpowers (S₁⁻¹ * S₂⁻¹) := by
  rw [modelCenter, Original.Z, MonoidHom.map_zpowers, ← Subgroup.zpowers_inv, ← map_inv,
    hW.modelHom_a_inv hn]

theorem center_eq_modelCenter [Finite G] (hn : 2 ≤ n) :
    (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype =
      modelCenter S (hW.equiv (by omega)) := by
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  rw [← Subgroup.map_center_eq (hW.equiv (by omega)).symm, Subgroup.map_map, hstr.center]
  rfl

theorem modelY_eq [Finite G] (hn : 2 ≤ n) :
    modelY S (hW.equiv (by omega)) =
      Subgroup.closure {S₁ * S₂⁻¹, T * S₁ ^ 2 ^ (n - 1)} := by
  have hm : 0 < 2 ^ n := pow_pos (by decide) n
  have hY : Original.Y (2 ^ n) =
      Subgroup.closure {Original.r (2 ^ n), Original.z (2 ^ n) * Original.x2 (2 ^ n)} := by
    have hzx2 : Original.z (2 ^ n) * Original.x2 (2 ^ n) =
        Original.r (2 ^ n) ^ (2 ^ n / 2) * Original.d (2 ^ n) := by
      rw [Original.d, Original.x2, Original.z, Original.s, Original.r_eq, element_base_pow,
        element_base_pow, element_base_mul, element_swap_mul, element_base_mul]
      simp only [nsmul_eq_mul, mul_one, mul_zero, mul_neg, add_zero, zero_add, element_eq_iff,
        and_true]
      have hhalf : ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) + ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) = 0 := by
        rw [← Nat.cast_add, ← two_mul, Nat.mul_div_cancel' (dvd_pow_self 2 (by omega)),
          ZMod.natCast_self]
      exact ⟨by linear_combination -hhalf, by linear_combination hhalf⟩
    apply le_antisymm
    · rw [Original.Y, Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · have hd : Original.d (2 ^ n) =
            (Original.r (2 ^ n) ^ (2 ^ n / 2))⁻¹ *
              (Original.z (2 ^ n) * Original.x2 (2 ^ n)) := by
          rw [hzx2]
          group
        rw [SetLike.mem_coe, hd]
        exact Subgroup.mul_mem _
          (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
          (Subgroup.subset_closure (by simp))
    · rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · rw [SetLike.mem_coe, hzx2]
        exact Subgroup.mul_mem _
          (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
          (Subgroup.subset_closure (by simp))
  rw [modelY, hY, MonoidHom.map_closure, Set.image_pair, hW.modelHom_r (by omega),
    hW.modelHom_swap_x2 (by omega)]

end WreathGenerators

end CFSG.Wreathed.BrauerWong
