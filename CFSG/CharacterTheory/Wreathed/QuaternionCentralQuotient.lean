module

public import CFSG.CharacterTheory.Wreathed.CentralizerFusion
public import CFSG.CharacterTheory.Semidihedral.CentralQuotients

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u

namespace Original

theorem Y_even (h : ℕ) : Y (2 * h) = quaternionSubgroup h := by
  rw [Y, r_eq, d_eq, show 2 * h / 2 = h by omega]
  exact (quaternion_range_eq_generated h).symm

theorem Y_map_modulus {m k : ℕ} (h : m = k) :
    (Y m).map (modulusEquiv h).toMonoidHom = Y k := by
  subst k
  simp [modulusEquiv]

end Original

@[expose] def originalYEvenEquiv (h : ℕ) :
    QuaternionGroup h ≃* Original.Y (2 * h) :=
  (quaternionRangeEquiv h).trans (MulEquiv.subgroupCongr (Original.Y_even h).symm)

theorem originalYEvenEquiv_coe_a (h : ℕ) (i : ZMod (2 * h)) :
    (originalYEvenEquiv h (QuaternionGroup.a i) : Wreath (2 * h)) =
      element (2 * h) i (-i) 0 := rfl

theorem originalYEvenEquiv_coe_xa (h : ℕ) (i : ZMod (2 * h)) :
    (originalYEvenEquiv h (QuaternionGroup.xa i) : Wreath (2 * h)) =
      element (2 * h) (h - i) i 1 := rfl

theorem originalYEvenEquiv_rotation (h : ℕ) :
    (originalYEvenEquiv h (QuaternionGroup.a 1) : Wreath (2 * h)) =
      Original.r (2 * h) := by
  rw [originalYEvenEquiv_coe_a, Original.r_eq]

theorem originalYEvenEquiv_generator (h : ℕ) :
    (originalYEvenEquiv h (QuaternionGroup.xa 0) : Wreath (2 * h)) =
      Original.d (2 * h) := by
  rw [originalYEvenEquiv_coe_xa, Original.d_eq, sub_zero,
    show 2 * h / 2 = h by omega]

theorem originalYEvenEquiv_involution (h : ℕ) :
    (originalYEvenEquiv h (QuaternionGroup.a (h : ZMod (2 * h))) : Wreath (2 * h)) =
      Original.x (2 * h) := by
  rw [originalYEvenEquiv_coe_a, Original.x_eq, half_modulus_neg,
    show 2 * h / 2 = h by omega]

theorem wreath_modulus_twice_half (n : ℕ) (hn : 1 ≤ n) :
    2 * (2 ^ n / 2) = 2 ^ n := by
  have hdiv : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
  exact Nat.mul_div_cancel' hdiv

@[expose] def originalYQuaternionEquiv (n : ℕ) (hn : 2 ≤ n) :
    QuaternionGroup (2 ^ n / 2) ≃* Original.Y (2 ^ n) :=
  (originalYEvenEquiv (2 ^ n / 2)).trans
    (((modulusEquiv (wreath_modulus_twice_half n (by omega))).subgroupMap
      (Original.Y (2 * (2 ^ n / 2)))).trans
      (MulEquiv.subgroupCongr (Original.Y_map_modulus
        (wreath_modulus_twice_half n (by omega)))))

theorem two_nsmul_eq_zero_twice_modulus (h : ℕ) (hh : 0 < h) (i : ZMod (2 * h)) :
    2 • i = 0 ↔ i = 0 ∨ i = (h : ℕ) := by
  let : NeZero (2 * h) := ⟨by omega⟩
  have hlt := ZMod.val_lt i
  have heq : 2 • i = ((2 * i.val : ℕ) : ZMod (2 * h)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]
  rw [heq, ZMod.natCast_eq_zero_iff,
    Nat.mul_dvd_mul_iff_left (by decide : 0 < (2 : ℕ))]
  constructor
  · rintro ⟨k, hk⟩
    have hklt : k < 2 := by nlinarith
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · left
      have hz : i.val = 0 := by simpa using hk
      rw [← ZMod.natCast_zmod_val i, hz, Nat.cast_zero]
    · right
      have hz : i.val = h := by simpa using hk
      rw [← ZMod.natCast_zmod_val i, hz]
  · rintro (rfl | rfl)
    · simp
    · rw [ZMod.val_natCast_of_lt (by omega)]

theorem nativeQuaternion_unique_involution (h : ℕ) (hh : 0 < h)
    (q : QuaternionGroup h) (hq : orderOf q = 2) :
    q = QuaternionGroup.a (h : ZMod (2 * h)) := by
  let : NeZero h := ⟨by omega⟩
  cases q with
  | a i =>
    have hs : 2 • i = 0 := by
      have hpow : (QuaternionGroup.a i : QuaternionGroup h) ^ 2 = 1 := by
        simpa only [hq] using pow_orderOf_eq_one (QuaternionGroup.a i : QuaternionGroup h)
      rw [pow_two, QuaternionGroup.a_mul_a] at hpow
      have hsum : i + i = 0 := QuaternionGroup.a.inj hpow
      simpa only [two_nsmul] using hsum
    rcases (two_nsmul_eq_zero_twice_modulus h hh i).mp hs with rfl | rfl
    · have hone : (QuaternionGroup.a 0 : QuaternionGroup h) = 1 := rfl
      rw [hone, orderOf_one] at hq
      omega
    · rfl
  | xa i =>
    rw [QuaternionGroup.orderOf_xa] at hq
    omega

theorem nativeQuaternion_center_eq (h : ℕ) (hh : 1 < h) :
    Subgroup.center (QuaternionGroup h) = CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ h := by
  let : NeZero h := ⟨by omega⟩
  apply le_antisymm
  · intro q hq
    cases q with
    | a i =>
      have hc := Subgroup.mem_center_iff.mp hq (QuaternionGroup.xa 0)
      rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa, zero_add, zero_sub] at hc
      have hi : i = -i := QuaternionGroup.xa.inj hc
      have hs : 2 • i = 0 := by
        rw [two_nsmul]
        calc i + i = i + -i := congrArg (i + ·) hi
             _ = 0 := add_neg_cancel i
      rcases (two_nsmul_eq_zero_twice_modulus h (by omega) i).mp hs with rfl | rfl
      · exact (CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ h).one_mem
      · exact Subgroup.mem_zpowers _
    | xa i =>
      have hc := Subgroup.mem_center_iff.mp hq (QuaternionGroup.a 1)
      rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hc
      have hi : i - 1 = i + 1 := QuaternionGroup.xa.inj hc
      have htwo : (2 : ZMod (2 * h)) = 0 := by linear_combination -hi
      have hdiv : 2 * h ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * h)).mp htwo
      have hle : 2 * h ≤ 2 := Nat.le_of_dvd (by decide) hdiv
      omega
  · exact Subgroup.zpowers_le.mpr (CFSG.Semidihedral.CentralQuotients.nativeQuaternion_half_mem_center h)

theorem modulusEquiv_original_r {m k : ℕ} (h : m = k) :
    modulusEquiv h (Original.r m) = Original.r k := by
  subst k
  rfl

theorem modulusEquiv_original_d {m k : ℕ} (h : m = k) :
    modulusEquiv h (Original.d m) = Original.d k := by
  subst k
  rfl

theorem modulusEquiv_original_x {m k : ℕ} (h : m = k) :
    modulusEquiv h (Original.x m) = Original.x k := by
  subst k
  rfl

theorem originalYQuaternionEquiv_rotation (n : ℕ) (hn : 2 ≤ n) :
    (originalYQuaternionEquiv n hn (QuaternionGroup.a 1) : Wreath (2 ^ n)) =
      Original.r (2 ^ n) := by
  change modulusEquiv (wreath_modulus_twice_half n (by omega))
    (originalYEvenEquiv (2 ^ n / 2) (QuaternionGroup.a 1) : Wreath (2 * (2 ^ n / 2))) = _
  rw [originalYEvenEquiv_rotation, modulusEquiv_original_r]

theorem originalYQuaternionEquiv_generator (n : ℕ) (hn : 2 ≤ n) :
    (originalYQuaternionEquiv n hn (QuaternionGroup.xa 0) : Wreath (2 ^ n)) =
      Original.d (2 ^ n) := by
  change modulusEquiv (wreath_modulus_twice_half n (by omega))
    (originalYEvenEquiv (2 ^ n / 2) (QuaternionGroup.xa 0) : Wreath (2 * (2 ^ n / 2))) = _
  rw [originalYEvenEquiv_generator, modulusEquiv_original_d]

theorem originalYQuaternionEquiv_involution (n : ℕ) (hn : 2 ≤ n) :
    (originalYQuaternionEquiv n hn
      (QuaternionGroup.a ((2 ^ n / 2 : ℕ) : ZMod (2 * (2 ^ n / 2)))) : Wreath (2 ^ n)) =
      Original.x (2 ^ n) := by
  change modulusEquiv (wreath_modulus_twice_half n (by omega))
    (originalYEvenEquiv (2 ^ n / 2)
      (QuaternionGroup.a ((2 ^ n / 2 : ℕ) : ZMod (2 * (2 ^ n / 2)))) :
        Wreath (2 * (2 ^ n / 2))) = _
  rw [originalYEvenEquiv_involution, modulusEquiv_original_x]

theorem original_x_mem_Y (n : ℕ) (hn : 2 ≤ n) :
    Original.x (2 ^ n) ∈ Original.Y (2 ^ n) :=
  (originalYQuaternionEquiv_involution n hn) ▸
    (originalYQuaternionEquiv n hn (QuaternionGroup.a ((2 ^ n / 2 : ℕ) :
      ZMod (2 * (2 ^ n / 2))))).property

@[expose] def originalYInvolution (n : ℕ) (hn : 2 ≤ n) : Original.Y (2 ^ n) :=
  ⟨Original.x (2 ^ n), original_x_mem_Y n hn⟩

@[expose] def originalYRotation (m : ℕ) : Original.Y m :=
  ⟨Original.r m, Subgroup.subset_closure (by simp)⟩

@[expose] def originalYGenerator (m : ℕ) : Original.Y m :=
  ⟨Original.d m, Subgroup.subset_closure (by simp)⟩

theorem originalY_unique_involution (n : ℕ) (hn : 2 ≤ n)
    (y : Original.Y (2 ^ n)) (hy : orderOf y = 2) : y = originalYInvolution n hn := by
  have hh : 0 < 2 ^ n / 2 := by
    have hpow : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega : 1 ≤ n)
    omega
  obtain ⟨q, rfl⟩ := (originalYQuaternionEquiv n hn).surjective y
  have hq : orderOf q = 2 := ((originalYQuaternionEquiv n hn).orderOf_eq q).symm.trans hy
  rw [nativeQuaternion_unique_involution _ hh q hq]
  apply Subtype.ext
  exact originalYQuaternionEquiv_involution n hn

theorem originalY_center_eq_zpowers (n : ℕ) (hn : 2 ≤ n) :
    Subgroup.center (Original.Y (2 ^ n)) = Subgroup.zpowers (originalYInvolution n hn) := by
  have hh : 1 < 2 ^ n / 2 := by
    have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  rw [← Subgroup.map_center_eq (originalYQuaternionEquiv n hn), nativeQuaternion_center_eq _ hh,
    CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ, MonoidHom.map_zpowers]
  congr 1
  exact Subtype.ext (originalYQuaternionEquiv_involution n hn)

theorem originalY_center_eq (n : ℕ) (hn : 2 ≤ n) :
    Subgroup.center (Original.Y (2 ^ n)) =
      (Subgroup.zpowers (Original.x (2 ^ n))).subgroupOf (Original.Y (2 ^ n)) := by
  apply Subgroup.map_subtype_inj.mp
  rw [originalY_center_eq_zpowers n hn, MonoidHom.map_zpowers,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr (original_x_mem_Y n hn))]
  rfl

theorem originalYCentralInvolution_normal (n : ℕ) (hn : 2 ≤ n) :
    ((Subgroup.zpowers (Original.x (2 ^ n))).subgroupOf (Original.Y (2 ^ n))).Normal := by
  rw [← originalY_center_eq n hn]
  infer_instance

theorem originalY_center_map (n : ℕ) (hn : 2 ≤ n) :
    (Subgroup.center (Original.Y (2 ^ n))).map (Original.Y (2 ^ n)).subtype =
      Subgroup.zpowers (Original.x (2 ^ n)) := by
  rw [originalY_center_eq_zpowers n hn, MonoidHom.map_zpowers]
  rfl

theorem originalY_is_nonabelian (n : ℕ) (hn : 2 ≤ n) :
    ∃ a b : Original.Y (2 ^ n), a * b ≠ b * a := by
  let E := originalYQuaternionEquiv n hn
  refine ⟨E (QuaternionGroup.a 1), E (QuaternionGroup.xa 0), ?_⟩
  intro heq
  have hsource : (QuaternionGroup.a 1 : QuaternionGroup (2 ^ n / 2)) * QuaternionGroup.xa 0 =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
    apply E.injective
    simpa only [map_mul] using heq
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, zero_sub, zero_add] at hsource
  have hsum : (2 : ZMod (2 * (2 ^ n / 2))) = 0 := by
    have hi : -(1 : ZMod (2 * (2 ^ n / 2))) = 1 := QuaternionGroup.xa.inj hsource
    linear_combination -hi
  have hdiv : 2 * (2 ^ n / 2) ∣ 2 :=
    (ZMod.natCast_eq_zero_iff 2 (2 * (2 ^ n / 2))).mp hsum
  rw [wreath_modulus_twice_half n (by omega)] at hdiv
  have hle : 2 ^ n ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  have hge : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  omega

theorem original_Z_inf_Y (n : ℕ) (hn : 2 ≤ n) :
    Original.Z (2 ^ n) ⊓ Original.Y (2 ^ n) = Subgroup.zpowers (Original.x (2 ^ n)) := by
  have hcenter := (wreath_center_involution_and_quaternion_coordinates n hn).nonabelian_centralizers
    (Original.Y (2 ^ n)) (originalY_is_nonabelian n hn)
  exact (inf_comm _ _).trans (hcenter.2.symm.trans (originalY_center_map n hn))

variable {G : Type u} [Group G]

@[expose] def modelYEquiv {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Original.Y m ≃* modelY S e :=
  (Original.Y m).equivMapOfInjective (wreathModelHom S e) (wreathModelHom_injective S e)

theorem modelYEquiv_coe {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) (y : Original.Y m) :
    (modelYEquiv S e y : G) = wreathModelHom S e y := rfl

theorem modelY_unique_involution (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : y ∈ modelY S e) (horder : orderOf y = 2) :
    y = wreathModelHom S e (Original.x (2 ^ n)) := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
  have hworder : orderOf (⟨w, hw⟩ : Original.Y (2 ^ n)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ((orderOf_injective _ (wreathModelHom_injective S e) w).symm.trans horder)
  have hweq := originalY_unique_involution n hn ⟨w, hw⟩ hworder
  exact congrArg (fun a : Original.Y (2 ^ n) => wreathModelHom S e a) hweq

theorem modelY_center_map (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (Subgroup.center (modelY S e)).map (modelY S e).subtype =
      Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n))) := by
  rw [← Subgroup.map_center_eq (modelYEquiv S e), Subgroup.map_map]
  change (Subgroup.center (Original.Y (2 ^ n))).map
    ((wreathModelHom S e).comp (Original.Y (2 ^ n)).subtype) = _
  rw [← Subgroup.map_map, originalY_center_map n hn, MonoidHom.map_zpowers]

theorem modelCenter_inf_modelY (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelCenter S e ⊓ modelY S e =
      Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n))) := by
  rw [modelCenter, modelY, ← Subgroup.map_inf _ _ _ (wreathModelHom_injective S e),
    original_Z_inf_Y n hn, MonoidHom.map_zpowers]

theorem modelY_center_eq (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.center (modelY S e) =
      (Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf (modelY S e) := by
  ext y
  change y ∈ Subgroup.center (modelY S e) ↔ y.val ∈
    Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))
  rw [← modelY_center_map n hn S e]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, heq⟩
    exact (Subtype.ext heq : z = y) ▸ hz

theorem originalYQuaternionEquiv_rotation_eq (n : ℕ) (hn : 2 ≤ n) :
    originalYQuaternionEquiv n hn (QuaternionGroup.a 1) = originalYRotation (2 ^ n) :=
  Subtype.ext (originalYQuaternionEquiv_rotation n hn)

theorem originalYQuaternionEquiv_generator_eq (n : ℕ) (hn : 2 ≤ n) :
    originalYQuaternionEquiv n hn (QuaternionGroup.xa 0) = originalYGenerator (2 ^ n) :=
  Subtype.ext (originalYQuaternionEquiv_generator n hn)

theorem originalYQuaternionEquiv_involution_eq (n : ℕ) (hn : 2 ≤ n) :
    originalYQuaternionEquiv n hn (QuaternionGroup.a ((2 ^ n / 2 : ℕ) :
      ZMod (2 * (2 ^ n / 2)))) = originalYInvolution n hn :=
  Subtype.ext (originalYQuaternionEquiv_involution n hn)

@[expose] def originalYCentralInvolution (n : ℕ) (hn : 2 ≤ n) :
    Subgroup (Original.Y (2 ^ n)) := Subgroup.zpowers (originalYInvolution n hn)

theorem originalYCentralInvolution_eq (n : ℕ) (hn : 2 ≤ n) :
    originalYCentralInvolution n hn =
      (Subgroup.zpowers (Original.x (2 ^ n))).subgroupOf (Original.Y (2 ^ n)) := by
  rw [originalYCentralInvolution, ← originalY_center_eq_zpowers n hn]
  exact originalY_center_eq n hn

instance originalYCentralInvolution_normal_instance (n : ℕ) (hn : 2 ≤ n) :
    (originalYCentralInvolution n hn).Normal := by
  rw [originalYCentralInvolution, ← originalY_center_eq_zpowers n hn]
  infer_instance

theorem originalYQuaternionEquiv_map_center (n : ℕ) (hn : 2 ≤ n) :
    (CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ (2 ^ n / 2)).map
      (originalYQuaternionEquiv n hn).toMonoidHom = originalYCentralInvolution n hn := by
  rw [CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ, MonoidHom.map_zpowers]
  change Subgroup.zpowers ((originalYQuaternionEquiv n hn)
    (QuaternionGroup.a ((2 ^ n / 2 : ℕ) : ZMod (2 * (2 ^ n / 2))))) = _
  rw [originalYQuaternionEquiv_involution_eq]
  rfl

@[expose] def originalYDihedralEquiv (n : ℕ) (hn : 2 ≤ n) :
    Original.Y (2 ^ n) ⧸ originalYCentralInvolution n hn ≃* DihedralGroup (2 ^ n / 2) := by
  let : NeZero (2 ^ n / 2) := ⟨by
    have hge : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega⟩
  exact (QuotientGroup.congr
    (CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ (2 ^ n / 2))
    (originalYCentralInvolution n hn)
    (originalYQuaternionEquiv n hn) (originalYQuaternionEquiv_map_center n hn)).symm.trans
    (CFSG.Semidihedral.CentralQuotients.nativeQuaternionQuotientEquiv (2 ^ n / 2)).symm

theorem originalYDihedralEquiv_mk (n : ℕ) (hn : 2 ≤ n)
    (q : QuaternionGroup (2 ^ n / 2)) :
    originalYDihedralEquiv n hn
      ((QuotientGroup.mk' (originalYCentralInvolution n hn)) (originalYQuaternionEquiv n hn q)) =
        CFSG.Semidihedral.CentralQuotients.quaternionToDihedral (2 ^ n / 2) q := by
  let : NeZero (2 ^ n / 2) := ⟨by
    have hge : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega⟩
  change (CFSG.Semidihedral.CentralQuotients.nativeQuaternionQuotientEquiv (2 ^ n / 2)).symm
    ((QuotientGroup.congr
      (CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ (2 ^ n / 2))
      (originalYCentralInvolution n hn) (originalYQuaternionEquiv n hn)
      (originalYQuaternionEquiv_map_center n hn)).symm
      ((QuotientGroup.mk' (originalYCentralInvolution n hn))
        (originalYQuaternionEquiv n hn q))) = _
  rw [← QuotientGroup.congr_mk'
    (CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ (2 ^ n / 2))
    (originalYCentralInvolution n hn) (originalYQuaternionEquiv n hn)
    (originalYQuaternionEquiv_map_center n hn) q, MulEquiv.symm_apply_apply]
  exact CFSG.Semidihedral.CentralQuotients.nativeQuaternionQuotientEquiv_symm_mk _ q

theorem originalYDihedralEquiv_rotation (n : ℕ) (hn : 2 ≤ n) :
    originalYDihedralEquiv n hn
      ((QuotientGroup.mk' (originalYCentralInvolution n hn)) (originalYRotation (2 ^ n))) =
        DihedralGroup.r 1 := by
  rw [← originalYQuaternionEquiv_rotation_eq n hn, originalYDihedralEquiv_mk]
  exact CFSG.Semidihedral.CentralQuotients.quaternionToDihedral_rotation _

theorem originalYDihedralEquiv_generator (n : ℕ) (hn : 2 ≤ n) :
    originalYDihedralEquiv n hn
      ((QuotientGroup.mk' (originalYCentralInvolution n hn)) (originalYGenerator (2 ^ n))) =
        DihedralGroup.sr 0 := by
  rw [← originalYQuaternionEquiv_generator_eq n hn, originalYDihedralEquiv_mk]
  exact CFSG.Semidihedral.CentralQuotients.quaternionToDihedral_generator _

theorem originalYDihedralQuotient_card (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Original.Y (2 ^ n) ⧸ originalYCentralInvolution n hn) = 2 ^ n := by
  rw [Nat.card_congr (originalYDihedralEquiv n hn).toEquiv, DihedralGroup.nat_card]
  exact wreath_modulus_twice_half n (by omega)

theorem originalYDihedralQuotient_isKleinFour :
    IsKleinFour (Original.Y (2 ^ 2) ⧸ originalYCentralInvolution 2 (by decide)) := by
  refine ⟨originalYDihedralQuotient_card 2 (by decide), ?_⟩
  rw [Monoid.exponent_eq_of_mulEquiv (originalYDihedralEquiv 2 (by decide))]
  exact DihedralGroup.exponent (n := 2) |>.trans (by decide)

@[expose] def modelYInvolution (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : modelY S e :=
  modelYEquiv S e (originalYInvolution n hn)

@[expose] def modelYRotation {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) : modelY S e :=
  modelYEquiv S e (originalYRotation m)

@[expose] def modelYGenerator {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) : modelY S e :=
  modelYEquiv S e (originalYGenerator m)

@[expose] def modelYCentralInvolution (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Subgroup (modelY S e) :=
  Subgroup.zpowers (modelYInvolution n hn S e)

theorem modelYInvolution_coe (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelYInvolution n hn S e : G) = wreathModelHom S e (Original.x (2 ^ n)) := rfl

theorem modelYRotation_coe {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (modelYRotation S e : G) = wreathModelHom S e (Original.r m) := rfl

theorem modelYGenerator_coe {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (modelYGenerator S e : G) = wreathModelHom S e (Original.d m) := rfl

theorem modelYEquiv_map_centralInvolution (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (originalYCentralInvolution n hn).map (modelYEquiv S e).toMonoidHom =
      modelYCentralInvolution n hn S e := by
  rw [originalYCentralInvolution, MonoidHom.map_zpowers]
  rfl

theorem modelYCentralInvolution_eq_center (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelYCentralInvolution n hn S e = Subgroup.center (modelY S e) := by
  rw [← modelYEquiv_map_centralInvolution n hn S e, originalYCentralInvolution,
    ← originalY_center_eq_zpowers n hn]
  exact Subgroup.map_center_eq (modelYEquiv S e)

instance modelYCentralInvolution_normal (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelYCentralInvolution n hn S e).Normal := by
  rw [modelYCentralInvolution_eq_center n hn S e]
  infer_instance

theorem modelYCentralInvolution_eq (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelYCentralInvolution n hn S e =
      (Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf (modelY S e) := by
  rw [modelYCentralInvolution_eq_center n hn S e]
  exact modelY_center_eq n hn S e

@[expose] def modelYDihedralEquiv (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelY S e ⧸ modelYCentralInvolution n hn S e ≃* DihedralGroup (2 ^ n / 2) :=
  (QuotientGroup.congr (originalYCentralInvolution n hn) (modelYCentralInvolution n hn S e)
    (modelYEquiv S e) (modelYEquiv_map_centralInvolution n hn S e)).symm.trans
      (originalYDihedralEquiv n hn)

theorem modelYDihedralEquiv_mk (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (y : Original.Y (2 ^ n)) :
    modelYDihedralEquiv n hn S e
      ((QuotientGroup.mk' (modelYCentralInvolution n hn S e)) (modelYEquiv S e y)) =
        originalYDihedralEquiv n hn ((QuotientGroup.mk' (originalYCentralInvolution n hn)) y) := by
  change originalYDihedralEquiv n hn
    ((QuotientGroup.congr (originalYCentralInvolution n hn) (modelYCentralInvolution n hn S e)
      (modelYEquiv S e) (modelYEquiv_map_centralInvolution n hn S e)).symm
        ((QuotientGroup.mk' (modelYCentralInvolution n hn S e)) (modelYEquiv S e y))) = _
  rw [← QuotientGroup.congr_mk' (originalYCentralInvolution n hn)
    (modelYCentralInvolution n hn S e) (modelYEquiv S e)
    (modelYEquiv_map_centralInvolution n hn S e) y, MulEquiv.symm_apply_apply]

theorem modelYDihedralEquiv_rotation (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelYDihedralEquiv n hn S e
      ((QuotientGroup.mk' (modelYCentralInvolution n hn S e)) (modelYRotation S e)) =
        DihedralGroup.r 1 := by
  rw [modelYRotation, modelYDihedralEquiv_mk]
  exact originalYDihedralEquiv_rotation n hn

theorem modelYDihedralEquiv_generator (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelYDihedralEquiv n hn S e
      ((QuotientGroup.mk' (modelYCentralInvolution n hn S e)) (modelYGenerator S e)) =
        DihedralGroup.sr 0 := by
  rw [modelYGenerator, modelYDihedralEquiv_mk]
  exact originalYDihedralEquiv_generator n hn

theorem modelYDihedralQuotient_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (modelY S e ⧸ modelYCentralInvolution n hn S e) = 2 ^ n := by
  rw [Nat.card_congr (modelYDihedralEquiv n hn S e).toEquiv, DihedralGroup.nat_card]
  exact wreath_modulus_twice_half n (by omega)

theorem modelYDihedralQuotient_isKleinFour (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ 2)) :
    IsKleinFour (modelY S e ⧸ modelYCentralInvolution 2 (by decide) S e) := by
  refine ⟨modelYDihedralQuotient_card 2 (by decide) S e, ?_⟩
  rw [Monoid.exponent_eq_of_mulEquiv (modelYDihedralEquiv 2 (by decide) S e)]
  exact DihedralGroup.exponent (n := 2) |>.trans (by decide)

theorem original_a_mem_center (m : ℕ) :
    Original.a m ∈ Subgroup.center (Wreath m) := by
  rw [Original.a_eq, Subgroup.mem_center_iff]
  intro g
  obtain ⟨⟨a, b, c⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  change element m a b c * element m 1 1 0 = element m 1 1 0 * element m a b c
  rcases swap_exponent_cases c with rfl | rfl
  · rw [element_base_mul, element_base_mul]
    congr 1 <;> abel
  · rw [element_swap_mul, element_base_mul, add_zero]
    congr 1 <;> abel

instance originalCyclicCenter_normal (m : ℕ) : (Original.Z m).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (original_a_mem_center m))

@[expose] def modelSylowCenter {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) : Subgroup S :=
  (modelCenter S e).subgroupOf (S : Subgroup G)

theorem modelSylowCenter_eq_map {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    modelSylowCenter S e = (Original.Z m).map e.symm.toMonoidHom := by
  ext s
  constructor
  · intro hs
    obtain ⟨z, hz, hval⟩ := Subgroup.mem_map.mp hs
    have heq : e.symm z = s := Subtype.ext hval
    exact Subgroup.mem_map.mpr ⟨z, hz, heq⟩
  · rintro ⟨z, hz, heq⟩
    change (s : G) ∈ modelCenter S e
    exact Subgroup.mem_map.mpr ⟨z, hz, congrArg Subtype.val heq⟩

instance modelSylowCenter_normal {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (modelSylowCenter S e).Normal := by
  rw [modelSylowCenter_eq_map]
  exact Subgroup.Normal.map inferInstance e.symm.toMonoidHom e.symm.surjective

theorem modelSylowCenter_eq_center (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelSylowCenter S e = Subgroup.center S := by
  rw [modelSylowCenter_eq_map, ← (wreath_center_involution_and_quaternion_coordinates n hn).center]
  exact Subgroup.map_center_eq e.symm

@[expose] def modelSylowDihedralEquiv (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    S ⧸ modelSylowCenter S e ≃* DihedralGroup (2 ^ n) :=
  (QuotientGroup.congr (Original.Z (2 ^ n)) (modelSylowCenter S e) e.symm
    (modelSylowCenter_eq_map S e).symm).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (wreath_center_involution_and_quaternion_coordinates n hn).center.symm).trans
        (centerQuotientEquivDihedral (2 ^ n) (by
          have hge : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
          omega)))

theorem centerQuotientEquivDihedral_mk (m : ℕ) (hm : 1 < m) (w : Wreath m) :
    centerQuotientEquivDihedral m hm ((QuotientGroup.mk' (Subgroup.center (Wreath m))) w) =
      dihedralProjection m w := rfl

theorem modelSylowDihedralEquiv_mk (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (w : Wreath (2 ^ n)) :
    modelSylowDihedralEquiv n hn S e
      ((QuotientGroup.mk' (modelSylowCenter S e)) (e.symm w)) =
        dihedralProjection (2 ^ n) w := by
  let E := QuotientGroup.congr (Original.Z (2 ^ n)) (modelSylowCenter S e) e.symm
    (modelSylowCenter_eq_map S e).symm
  change centerQuotientEquivDihedral (2 ^ n) (by
    have hge : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega)
    ((QuotientGroup.quotientMulEquivOfEq
      (wreath_center_involution_and_quaternion_coordinates n hn).center.symm)
      (E.symm ((QuotientGroup.mk' (modelSylowCenter S e)) (e.symm w)))) = _
  rw [← QuotientGroup.congr_mk' (Original.Z (2 ^ n)) (modelSylowCenter S e) e.symm
    (modelSylowCenter_eq_map S e).symm w, MulEquiv.symm_apply_apply]
  rfl

theorem modelSylowDihedralEquiv_mk_coordinates (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (a b : ZMod (2 ^ n)) (c : ZMod 2) :
    modelSylowDihedralEquiv n hn S e
      ((QuotientGroup.mk' (modelSylowCenter S e)) (e.symm (element (2 ^ n) a b c))) =
        if c = 0 then DihedralGroup.r (a - b) else DihedralGroup.sr (b - a) := by
  rw [modelSylowDihedralEquiv_mk]
  rfl

theorem modelSylowDihedralEquiv_s (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelSylowDihedralEquiv n hn S e
      ((QuotientGroup.mk' (modelSylowCenter S e)) (e.symm (Original.s (2 ^ n)))) =
        DihedralGroup.r 1 := by
  rw [Original.s, modelSylowDihedralEquiv_mk_coordinates]
  simp

theorem modelSylowDihedralEquiv_t (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelSylowDihedralEquiv n hn S e
      ((QuotientGroup.mk' (modelSylowCenter S e)) (e.symm (Original.t (2 ^ n)))) =
        DihedralGroup.r (-1) := by
  rw [Original.t, modelSylowDihedralEquiv_mk_coordinates]
  simp

theorem modelSylowDihedralEquiv_z (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelSylowDihedralEquiv n hn S e
      ((QuotientGroup.mk' (modelSylowCenter S e)) (e.symm (Original.z (2 ^ n)))) =
        DihedralGroup.sr 0 := by
  rw [Original.z, modelSylowDihedralEquiv_mk_coordinates]
  simp

theorem modelSylowDihedralQuotient_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (S ⧸ modelSylowCenter S e) = 2 * 2 ^ n := by
  rw [Nat.card_congr (modelSylowDihedralEquiv n hn S e).toEquiv, DihedralGroup.nat_card]

theorem modelYDihedralEquiv_symm_rotation (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelYDihedralEquiv n hn S e).symm (DihedralGroup.r 1) =
      (QuotientGroup.mk' (modelYCentralInvolution n hn S e)) (modelYRotation S e) := by
  apply (modelYDihedralEquiv n hn S e).injective
  rw [MulEquiv.apply_symm_apply, modelYDihedralEquiv_rotation]

theorem modelYDihedralEquiv_symm_generator (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelYDihedralEquiv n hn S e).symm (DihedralGroup.sr 0) =
      (QuotientGroup.mk' (modelYCentralInvolution n hn S e)) (modelYGenerator S e) := by
  apply (modelYDihedralEquiv n hn S e).injective
  rw [MulEquiv.apply_symm_apply, modelYDihedralEquiv_generator]

theorem centralizerQuaternion_unique_involution (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : involutionCentralizer n S e) (hy : y ∈ centralizerQuaternion n hn S e)
    (horder : orderOf y = 2) : y = centralInvolution n S e := by
  exact modelY_unique_involution n hn (centralizerSylow n hn S e)
    (centralizerCoordinates n hn S e) y hy horder

theorem centralizerQuaternion_full_center_intersection (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelCenter (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) ⊓
      centralizerQuaternion n hn S e = Subgroup.zpowers (centralInvolution n S e) :=
  modelCenter_inf_modelY n hn (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)

theorem originalY_literal_dihedral_quotient (n : ℕ) (hn : 2 ≤ n) :
    ∃ h : ((Subgroup.zpowers (Original.x (2 ^ n))).subgroupOf (Original.Y (2 ^ n))).Normal,
      letI := h
      ∃ E : Original.Y (2 ^ n) ⧸
          (Subgroup.zpowers (Original.x (2 ^ n))).subgroupOf (Original.Y (2 ^ n)) ≃*
            DihedralGroup (2 ^ n / 2),
        E ((QuotientGroup.mk' ((Subgroup.zpowers (Original.x (2 ^ n))).subgroupOf
          (Original.Y (2 ^ n)))) (originalYRotation (2 ^ n))) = DihedralGroup.r 1 ∧
        E ((QuotientGroup.mk' ((Subgroup.zpowers (Original.x (2 ^ n))).subgroupOf
          (Original.Y (2 ^ n)))) (originalYGenerator (2 ^ n))) = DihedralGroup.sr 0 := by
  let : ((Subgroup.zpowers (Original.x (2 ^ n))).subgroupOf
      (Original.Y (2 ^ n))).Normal := originalYCentralInvolution_normal n hn
  refine ⟨inferInstance, ?_⟩
  let E := (QuotientGroup.quotientMulEquivOfEq (originalYCentralInvolution_eq n hn).symm).trans
    (originalYDihedralEquiv n hn)
  exact ⟨E, originalYDihedralEquiv_rotation n hn, originalYDihedralEquiv_generator n hn⟩

theorem modelY_literal_dihedral_quotient (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ∃ h : ((Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf
        (modelY S e)).Normal,
      letI := h
      ∃ E : modelY S e ⧸
          (Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf
            (modelY S e) ≃* DihedralGroup (2 ^ n / 2),
        E ((QuotientGroup.mk' ((Subgroup.zpowers
          (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf (modelY S e)))
            (modelYRotation S e)) = DihedralGroup.r 1 ∧
        E ((QuotientGroup.mk' ((Subgroup.zpowers
          (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf (modelY S e)))
            (modelYGenerator S e)) = DihedralGroup.sr 0 := by
  have hC : ((Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf
      (modelY S e)).Normal := by
    rw [← modelY_center_eq n hn S e]
    infer_instance
  refine ⟨hC, ?_⟩
  let E := (QuotientGroup.quotientMulEquivOfEq
    (modelYCentralInvolution_eq n hn S e).symm).trans (modelYDihedralEquiv n hn S e)
  exact ⟨E, modelYDihedralEquiv_rotation n hn S e, modelYDihedralEquiv_generator n hn S e⟩

theorem wreathed_quaternion_and_full_center_dihedral_quotients
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (∀ y : Original.Y (2 ^ n), orderOf y = 2 → y = originalYInvolution n hn) ∧
    Subgroup.center (Original.Y (2 ^ n)) =
      (Subgroup.zpowers (Original.x (2 ^ n))).subgroupOf (Original.Y (2 ^ n)) ∧
    Original.Z (2 ^ n) ⊓ Original.Y (2 ^ n) = Subgroup.zpowers (Original.x (2 ^ n)) ∧
    (∀ y : G, y ∈ modelY S e → orderOf y = 2 →
      y = wreathModelHom S e (Original.x (2 ^ n))) ∧
    Subgroup.center (modelY S e) =
      (Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf (modelY S e) ∧
    modelCenter S e ⊓ modelY S e =
      Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n))) ∧
    (∃ E : modelY S e ⧸ modelYCentralInvolution n hn S e ≃* DihedralGroup (2 ^ n / 2),
      E ((QuotientGroup.mk' (modelYCentralInvolution n hn S e)) (modelYRotation S e)) =
        DihedralGroup.r 1 ∧
      E ((QuotientGroup.mk' (modelYCentralInvolution n hn S e)) (modelYGenerator S e)) =
        DihedralGroup.sr 0) ∧
    Nat.card (modelY S e ⧸ modelYCentralInvolution n hn S e) = 2 ^ n ∧
    (∃ E : S ⧸ modelSylowCenter S e ≃* DihedralGroup (2 ^ n),
      ∀ w : Wreath (2 ^ n), E ((QuotientGroup.mk' (modelSylowCenter S e)) (e.symm w)) =
        dihedralProjection (2 ^ n) w) ∧
    Nat.card (S ⧸ modelSylowCenter S e) = 2 * 2 ^ n := by
  exact ⟨originalY_unique_involution n hn, originalY_center_eq n hn, original_Z_inf_Y n hn,
    modelY_unique_involution n hn S e, modelY_center_eq n hn S e,
    modelCenter_inf_modelY n hn S e,
    ⟨modelYDihedralEquiv n hn S e, modelYDihedralEquiv_rotation n hn S e,
      modelYDihedralEquiv_generator n hn S e⟩,
    modelYDihedralQuotient_card n hn S e,
    ⟨modelSylowDihedralEquiv n hn S e, modelSylowDihedralEquiv_mk n hn S e⟩,
    modelSylowDihedralQuotient_card n hn S e⟩


theorem originalYInvolution_orderOf (n : ℕ) (hn : 2 ≤ n) :
    orderOf (originalYInvolution n hn) = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1

theorem originalY_exists_unique_involution (n : ℕ) (hn : 2 ≤ n) :
    ∃! y : Original.Y (2 ^ n), orderOf y = 2 := by
  exact ⟨originalYInvolution n hn, originalYInvolution_orderOf n hn,
    originalY_unique_involution n hn⟩

theorem modelYInvolution_orderOf (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderOf (modelYInvolution n hn S e) = 2 := by
  rw [modelYInvolution, (modelYEquiv S e).orderOf_eq]
  exact originalYInvolution_orderOf n hn

theorem modelY_exists_unique_involution (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ∃! y : modelY S e, orderOf y = 2 := by
  refine ⟨modelYInvolution n hn S e, modelYInvolution_orderOf n hn S e, ?_⟩
  intro y hy
  apply Subtype.ext
  exact modelY_unique_involution n hn S e y y.property
    ((Subgroup.orderOf_coe y).trans hy)

theorem originalY_literal_dihedral_quotient_card (n : ℕ) (hn : 2 ≤ n) :
    ∃ h : ((Subgroup.zpowers (Original.x (2 ^ n))).subgroupOf
        (Original.Y (2 ^ n))).Normal,
      letI := h
      Nat.card (Original.Y (2 ^ n) ⧸
        (Subgroup.zpowers (Original.x (2 ^ n))).subgroupOf (Original.Y (2 ^ n))) = 2 ^ n := by
  let : ((Subgroup.zpowers (Original.x (2 ^ n))).subgroupOf
      (Original.Y (2 ^ n))).Normal := originalYCentralInvolution_normal n hn
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
    (originalYCentralInvolution_eq n hn).symm).toEquiv]
  exact originalYDihedralQuotient_card n hn

theorem modelY_literal_dihedral_quotient_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ∃ h : ((Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf
        (modelY S e)).Normal,
      letI := h
      Nat.card (modelY S e ⧸
        (Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf
          (modelY S e)) = 2 ^ n := by
  let : ((Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf
      (modelY S e)).Normal := by
    rw [← modelY_center_eq n hn S e]
    infer_instance
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
    (modelYCentralInvolution_eq n hn S e).symm).toEquiv]
  exact modelYDihedralQuotient_card n hn S e

theorem originalY_literal_dihedral_quotient_isKleinFour :
    ∃ h : ((Subgroup.zpowers (Original.x (2 ^ 2))).subgroupOf (Original.Y (2 ^ 2))).Normal,
      letI := h
      IsKleinFour (Original.Y (2 ^ 2) ⧸
        (Subgroup.zpowers (Original.x (2 ^ 2))).subgroupOf (Original.Y (2 ^ 2))) := by
  let : ((Subgroup.zpowers (Original.x (2 ^ 2))).subgroupOf
      (Original.Y (2 ^ 2))).Normal := originalYCentralInvolution_normal 2 (by decide)
  refine ⟨inferInstance, ?_⟩
  let E := (QuotientGroup.quotientMulEquivOfEq
    (originalYCentralInvolution_eq 2 (by decide)).symm).trans
    (originalYDihedralEquiv 2 (by decide))
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr E.toEquiv, DihedralGroup.nat_card]
    rfl
  · rw [Monoid.exponent_eq_of_mulEquiv E]
    exact DihedralGroup.exponent (n := 2) |>.trans (by decide)

theorem modelY_literal_dihedral_quotient_isKleinFour
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ 2)) :
    ∃ h : ((Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ 2)))).subgroupOf
        (modelY S e)).Normal,
      letI := h
      IsKleinFour (modelY S e ⧸
        (Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ 2)))).subgroupOf
          (modelY S e)) := by
  let : ((Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ 2)))).subgroupOf
      (modelY S e)).Normal := by
    rw [← modelY_center_eq 2 (by decide) S e]
    infer_instance
  refine ⟨inferInstance, ?_⟩
  let E := (QuotientGroup.quotientMulEquivOfEq
    (modelYCentralInvolution_eq 2 (by decide) S e).symm).trans
    (modelYDihedralEquiv 2 (by decide) S e)
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr E.toEquiv, DihedralGroup.nat_card]
    rfl
  · rw [Monoid.exponent_eq_of_mulEquiv E]
    exact DihedralGroup.exponent (n := 2) |>.trans (by decide)

end CFSG.Wreathed
