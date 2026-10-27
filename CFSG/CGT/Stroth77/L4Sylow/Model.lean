module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Ref

public section

namespace CFSG.CGT.Stroth77.L4Sylow

open Equiv CFSG.GH74.GLS.Stage1.Thm3.Sec8

@[expose] def permAut (n : ℕ) (π : Perm (Fin 4)) :
    MulAut (Multiplicative (Fin 4 → ZMod (2 ^ n))) where
  toFun d := Multiplicative.ofAdd fun i => Multiplicative.toAdd d (π⁻¹ i)
  invFun d := Multiplicative.ofAdd fun i => Multiplicative.toAdd d (π i)
  left_inv d := by simp
  right_inv d := by simp
  map_mul' d e := by
    simp only [toAdd_mul]
    rfl

@[expose] def permAct (n : ℕ) : Perm (Fin 4) →* MulAut (Multiplicative (Fin 4 → ZMod (2 ^ n))) where
  toFun := permAut n
  map_one' := by
    refine MulEquiv.ext fun d => ?_
    rfl
  map_mul' π σ := by
    refine MulEquiv.ext fun d => ?_
    rfl

@[expose] def actL4 (n : ℕ) : Fin81.R0 →* MulAut (Multiplicative (Fin 4 → ZMod (2 ^ n))) :=
  (permAct n).comp Fin81.R0.subtype

theorem toAdd_actL4 (n : ℕ) (π : Fin81.R0) (d : Multiplicative (Fin 4 → ZMod (2 ^ n)))
    (i : Fin 4) :
    Multiplicative.toAdd (actL4 n π d) i = Multiplicative.toAdd d ((π : Perm (Fin 4))⁻¹ i) :=
  rfl

abbrev L4Hat (n : ℕ) := Multiplicative (Fin 4 → ZMod (2 ^ n)) ⋊[actL4 n] Fin81.R0

theorem card_L4Hat (n : ℕ) : Nat.card (L4Hat n) = 2 ^ (4 * n + 3) := by
  rw [SemidirectProduct.card, Fin81.card_R0, Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp only [Nat.card_zmod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem two_pow_pred_add_self (n : ℕ) :
    ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) + ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) = 0 := by
  rcases n with _ | n
  · change ((2 ^ (0 - 1) : ℕ) : ZMod 1) + ((2 ^ (0 - 1) : ℕ) : ZMod 1) = 0
    exact Subsingleton.elim _ _
  · rw [← Nat.cast_add, Nat.add_sub_cancel, ← two_mul, ← pow_succ']
    exact ZMod.natCast_self _

@[expose] def signZ (n : ℕ) : ℤˣ →* Multiplicative (ZMod (2 ^ n)) where
  toFun u := if u = 1 then 1 else Multiplicative.ofAdd ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl
    · simp
    · simp
    · simp
    · have h : ((-1 : ℤˣ) * -1) = 1 := by decide
      rw [h, if_pos rfl, if_neg (by decide), ← ofAdd_add, two_pow_pred_add_self]
      rfl

theorem signZ_one (n : ℕ) : signZ n 1 = 1 := map_one _

theorem signZ_neg_one (n : ℕ) :
    signZ n (-1) = Multiplicative.ofAdd ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) := by
  show (if (-1 : ℤˣ) = 1 then (1 : Multiplicative (ZMod (2 ^ n))) else
    Multiplicative.ofAdd ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))) = _
  exact if_neg (by decide)

@[expose] def sumL4 (n : ℕ) : Multiplicative (Fin 4 → ZMod (2 ^ n)) →* Multiplicative (ZMod (2 ^ n))
    where
  toFun d := Multiplicative.ofAdd (∑ i, Multiplicative.toAdd d i)
  map_one' := by simp
  map_mul' d e := by
    simp only [toAdd_mul, Pi.add_apply, Finset.sum_add_distrib]
    rfl

theorem sumL4_actL4 (n : ℕ) (π : Fin81.R0) (d : Multiplicative (Fin 4 → ZMod (2 ^ n))) :
    sumL4 n (actL4 n π d) = sumL4 n d := by
  change Multiplicative.ofAdd (∑ i, Multiplicative.toAdd d ((π : Perm (Fin 4))⁻¹ i)) = _
  rw [Equiv.sum_comp ((π : Perm (Fin 4))⁻¹) (fun i => Multiplicative.toAdd d i)]
  rfl

@[expose] def detL4 (n : ℕ) : L4Hat n →* Multiplicative (ZMod (2 ^ n)) :=
  SemidirectProduct.lift (sumL4 n) ((signZ n).comp (Perm.sign.comp Fin81.R0.subtype))
    fun π => by
      refine MonoidHom.ext fun d => ?_
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_comm, inv_mul_cancel_left, sumL4_actL4]

theorem detL4_apply (n : ℕ) (a : L4Hat n) :
    Multiplicative.toAdd (detL4 n a) = (∑ i, Multiplicative.toAdd a.left i) +
      Multiplicative.toAdd (signZ n (Perm.sign (a.right : Perm (Fin 4)))) := rfl

theorem detL4_surjective (n : ℕ) : Function.Surjective (detL4 n) := by
  intro z
  refine ⟨⟨Multiplicative.ofAdd (Pi.single 0 (Multiplicative.toAdd z)), 1⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [detL4_apply]
  simp [signZ]

abbrev L4P (n : ℕ) : Subgroup (L4Hat n) := (detL4 n).ker

theorem mem_L4P {n : ℕ} {a : L4Hat n} : a ∈ L4P n ↔ detL4 n a = 1 := MonoidHom.mem_ker

theorem card_L4P (n : ℕ) : Nat.card (L4P n) = 2 ^ (3 * n + 3) := by
  have h := Subgroup.card_ker_mul_card_of_surjective (detL4_surjective n)
  rw [card_L4Hat, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
  have h2 : 2 ^ (4 * n + 3) = 2 ^ (3 * n + 3) * 2 ^ n := by rw [← pow_add]; ring_nf
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

abbrev zL4 (n : ℕ) : ZMod (2 ^ n) := ((2 ^ (n - 2) : ℕ) : ZMod (2 ^ n))

theorem four_mul_zL4 (n : ℕ) : 4 * zL4 n = 0 := by
  rcases n with _ | _ | n
  · change (4 : ZMod 1) * _ = 0
    exact Subsingleton.elim _ _
  · change (4 : ZMod 2) * _ = 0
    rw [show (4 : ZMod 2) = 0 from rfl, zero_mul]
  · rw [zL4, show (4 : ZMod (2 ^ (n + 2))) = ((4 : ℕ) : ZMod (2 ^ (n + 2))) by norm_num,
      ← Nat.cast_mul, show 4 * 2 ^ (n + 2 - 2) = 2 ^ (n + 2) by
        rw [show n + 2 - 2 = n by omega]; ring, ZMod.natCast_self]

@[expose] def cHat (n : ℕ) : L4Hat n := ⟨Multiplicative.ofAdd fun _ => zL4 n, 1⟩

theorem cHat_mem (n : ℕ) : cHat n ∈ L4P n := by
  rw [mem_L4P]
  apply Multiplicative.toAdd.injective
  rw [detL4_apply]
  have h1 : (∑ i : Fin 4, Multiplicative.toAdd (cHat n).left i) = 4 * zL4 n := by
    rw [show (cHat n).left = Multiplicative.ofAdd (fun _ => zL4 n) from rfl, toAdd_ofAdd,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have h2 : ((cHat n).right : Perm (Fin 4)) = 1 := rfl
  rw [h1, h2, map_one, map_one, four_mul_zL4, toAdd_one, zero_add]

theorem cHat_mul_comm (n : ℕ) (a : L4Hat n) : cHat n * a = a * cHat n := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    simp only [SemidirectProduct.mul_left, cHat, map_one, MulAut.one_apply, toAdd_mul,
      Pi.add_apply, toAdd_ofAdd]
    rw [toAdd_actL4]
    simp only [toAdd_ofAdd]
    ring
  · simp [cHat]

@[expose] def cL4 (n : ℕ) : L4P n := ⟨cHat n, cHat_mem n⟩

theorem coe_cL4 (n : ℕ) : ((cL4 n : L4P n) : L4Hat n) = cHat n := rfl

theorem cL4_mem_center (n : ℕ) : cL4 n ∈ Subgroup.center (L4P n) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact (cHat_mul_comm n g).symm

instance (n : ℕ) : (Subgroup.zpowers (cL4 n)).Normal :=
  Subgroup.normal_of_le_center ((Subgroup.zpowers_le).mpr (cL4_mem_center n))

abbrev L4Model (n : ℕ) := L4P n ⧸ Subgroup.zpowers (cL4 n)

theorem orderOf_cL4 {n : ℕ} (hn : 2 ≤ n) : orderOf (cL4 n) = 4 := by
  rw [← Subgroup.orderOf_coe, coe_cL4]
  have hinl : cHat n = SemidirectProduct.inl (Multiplicative.ofAdd fun _ => zL4 n) := rfl
  rw [hinl, orderOf_injective _ SemidirectProduct.inl_injective, orderOf_ofAdd_eq_addOrderOf]
  have hconst : (fun _ : Fin 4 => zL4 n) = Pi.constAddMonoidHom (Fin 4) (ZMod (2 ^ n)) (zL4 n) :=
    rfl
  rw [hconst, addOrderOf_injective _ (fun x y h => congrFun h 0), zL4,
    ZMod.addOrderOf_coe _ (by positivity), Nat.gcd_eq_right (pow_dvd_pow 2 (Nat.sub_le n 2)),
    Nat.pow_div (Nat.sub_le n 2) (by norm_num), show n - (n - 2) = 2 by omega]

theorem card_L4Model {n : ℕ} (hn : 2 ≤ n) : Nat.card (L4Model n) = 2 ^ (3 * n + 1) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (cL4 n))
  rw [card_L4P, Nat.card_zpowers, orderOf_cL4 hn] at h
  have h2 : 2 ^ (3 * n + 3) = 2 ^ (3 * n + 1) * 4 := by rw [pow_add, pow_add]; ring
  rw [h2] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm

theorem cHat_zpow (n : ℕ) (k : ℤ) :
    cHat n ^ k = ⟨Multiplicative.ofAdd fun _ => k • zL4 n, 1⟩ := by
  have hinl : cHat n = SemidirectProduct.inl (Multiplicative.ofAdd fun _ => zL4 n) := rfl
  rw [hinl, ← map_zpow, ← ofAdd_zsmul]
  rfl

theorem exists_eq_nsmul_zL4 {n : ℕ} (hn : 2 ≤ n) {x : ZMod (2 ^ n)} (hx : 4 * x = 0) :
    ∃ j : ℕ, x = j • zL4 n := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  have hx' : ((4 * x.val : ℕ) : ZMod (2 ^ n)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact_mod_cast hx
  rw [ZMod.natCast_eq_zero_iff] at hx'
  have h4 : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have hx'' : 4 * 2 ^ (n - 2) ∣ 4 * x.val := by rw [← h4]; exact hx'
  obtain ⟨j, hj⟩ := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 4)).mp hx''
  refine ⟨j, ?_⟩
  rw [nsmul_eq_mul, zL4, ← Nat.cast_mul, mul_comm, ← hj, ZMod.natCast_zmod_val]

theorem mem_zpowers_cL4 {n : ℕ} (hn : 2 ≤ n) {a : L4P n} :
    a ∈ Subgroup.zpowers (cL4 n) ↔ ((a : L4Hat n).right = 1 ∧
      ∀ i j, Multiplicative.toAdd (a : L4Hat n).left i =
        Multiplicative.toAdd (a : L4Hat n).left j) := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rw [Subgroup.coe_zpow, coe_cL4, cHat_zpow]
    exact ⟨rfl, fun _ _ => rfl⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨al, ar⟩ := (a : L4Hat n)
    have hdet := mem_L4P.mp a.2
    have hsum : 4 * Multiplicative.toAdd (a : L4Hat n).left 0 = 0 := by
      have h := congrArg Multiplicative.toAdd hdet
      rw [detL4_apply, h1, OneMemClass.coe_one, map_one, map_one, toAdd_one, add_zero,
        Fin.sum_univ_four, ← h2 0 1, ← h2 0 2, ← h2 0 3] at h
      rw [← h]
      ring
    obtain ⟨j, hj⟩ := exists_eq_nsmul_zL4 hn hsum
    refine ⟨(j : ℤ), Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, coe_cL4, cHat_zpow]
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      rw [toAdd_ofAdd, natCast_zsmul, h2 i 0, hj]
    · exact h1.symm

end CFSG.CGT.Stroth77.L4Sylow
