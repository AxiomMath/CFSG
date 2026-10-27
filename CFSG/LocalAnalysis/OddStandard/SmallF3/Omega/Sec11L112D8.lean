module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

@[expose] def sec11Pw (a : G) (k : ZMod 4) : G := a ^ k.val

theorem sec11Pw_add {a : G} (ha4 : a ^ 4 = 1) (k l : ZMod 4) :
    sec11Pw a (k + l) = sec11Pw a k * sec11Pw a l := by
  unfold sec11Pw
  rw [ZMod.val_add, ← pow_add, pow_eq_pow_mod (k.val + l.val) ha4]

theorem sec11Pw_zero (a : G) : sec11Pw a 0 = 1 := by
  simp [sec11Pw]

theorem sec11Pw_neg {a : G} (ha4 : a ^ 4 = 1) (k : ZMod 4) :
    sec11Pw a (-k) = (sec11Pw a k)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← sec11Pw_add ha4, add_neg_cancel, sec11Pw_zero]

theorem sec11Pw_conj {a b : G} (ha4 : a ^ 4 = 1) (hb2 : b * b = 1) (hba : b * a * b = a⁻¹)
    (k : ZMod 4) : b * sec11Pw a k = sec11Pw a (-k) * b := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have h1 : b * a ^ k.val * b = (a⁻¹) ^ k.val := by
    have h := conj_pow (a := b) (b := a) (i := k.val)
    rw [hbinv] at h
    rw [← h, hba]
  have h2 : b * a ^ k.val * b = sec11Pw a (-k) := by
    rw [h1, sec11Pw_neg ha4, inv_pow]
    rfl
  calc b * sec11Pw a k = b * a ^ k.val * (b * b) := by
        rw [hb2, mul_one]
        rfl
    _ = (b * a ^ k.val * b) * b := (mul_assoc _ _ _).symm
    _ = sec11Pw a (-k) * b := by rw [h2]

@[expose] def sec11D8Hom (a b : G) (ha4 : a ^ 4 = 1) (hb2 : b * b = 1) (hba : b * a * b = a⁻¹) :
    DihedralGroup 4 →* G :=
  MonoidHom.mk' (fun x => match x with
    | DihedralGroup.r i => sec11Pw a i
    | DihedralGroup.sr i => sec11Pw a (-i) * b) (by
    intro x y
    have hc := sec11Pw_conj ha4 hb2 hba
    have hp := sec11Pw_add ha4
    rcases x with i | i <;> rcases y with j | j
    · exact hp i j
    · show sec11Pw a (-(j - i)) * b = sec11Pw a i * (sec11Pw a (-j) * b)
      rw [← mul_assoc, ← hp]
      have : -(j - i) = i + -j := by ring
      rw [this]
    · show sec11Pw a (-(i + j)) * b = sec11Pw a (-i) * b * sec11Pw a j
      rw [mul_assoc, hc j, ← mul_assoc, ← hp]
      have : -(i + j) = -i + -j := by ring
      rw [this]
    · show sec11Pw a (j - i) = sec11Pw a (-i) * b * (sec11Pw a (-j) * b)
      rw [mul_assoc, ← mul_assoc b, hc (-j), neg_neg, mul_assoc (sec11Pw a j) b b, hb2, mul_one,
        ← hp]
      have : j - i = -i + j := by ring
      rw [this])

theorem sec11D8Hom_injective {a b : G} (ha4 : a ^ 4 = 1) (hb2 : b * b = 1)
    (hba : b * a * b = a⁻¹) (ha2 : a ^ 2 ≠ 1) :
    Function.Injective (sec11D8Hom a b ha4 hb2 hba) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf a = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a) (by simpa using ha2)
      (by simpa using ha4)
    simpa using this
  rw [injective_iff_map_eq_one]
  intro x hx
  rcases x with i | i
  · have h : sec11Pw a i = 1 := hx
    have hdvd : 4 ∣ i.val := by
      have h' : orderOf a ∣ i.val := orderOf_dvd_of_pow_eq_one h
      rwa [hord] at h'
    have hlt : i.val < 4 := ZMod.val_lt i
    have h0 : i.val = 0 := by omega
    have : i = 0 := (ZMod.val_eq_zero i).mp h0
    rw [this]
    rfl
  · exfalso
    have h : sec11Pw a (-i) * b = 1 := hx
    have hb : b = sec11Pw a i := by
      have h1 : b = (sec11Pw a (-i))⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h1, sec11Pw_neg ha4, inv_inv]
    have hcomm : b * a = a * b := by
      rw [hb]
      exact ((Commute.refl a).pow_left i.val).eq
    apply ha2
    have hinv : a = a⁻¹ := by
      rw [← hba, hcomm, mul_assoc, hb2, mul_one]
    calc a ^ 2 = a * a := pow_two a
      _ = a * a⁻¹ := by rw [← hinv]
      _ = 1 := mul_inv_cancel a

theorem sec11D8Hom_range {a b : G} (ha4 : a ^ 4 = 1) (hb2 : b * b = 1)
    (hba : b * a * b = a⁻¹) :
    (sec11D8Hom a b ha4 hb2 hba).range = zpowers a ⊔ zpowers b := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rcases x with i | i
    · exact mem_sup_left (pow_mem (mem_zpowers a) _)
    · exact mul_mem (mem_sup_left (pow_mem (mem_zpowers a) _)) (mem_sup_right (mem_zpowers b))
  · refine sup_le (zpowers_le.mpr ⟨DihedralGroup.r 1, ?_⟩) (zpowers_le.mpr ⟨DihedralGroup.sr 0, ?_⟩)
    · show sec11Pw a 1 = a
      have : (1 : ZMod 4).val = 1 := rfl
      rw [sec11Pw, this, pow_one]
    · show sec11Pw a (-0) * b = b
      rw [neg_zero, sec11Pw_zero, one_mul]

theorem sec11_isD8_of_ab {a b : G} (ha4 : a ^ 4 = 1) (hb2 : b * b = 1) (hba : b * a * b = a⁻¹)
    (ha2 : a ^ 2 ≠ 1) : IsD8 (zpowers a ⊔ zpowers b) := by
  have hinj := sec11D8Hom_injective ha4 hb2 hba ha2
  let e1 : DihedralGroup 4 ≃* ↥(sec11D8Hom a b ha4 hb2 hba).range := MonoidHom.ofInjective hinj
  let e2 : ↥(sec11D8Hom a b ha4 hb2 hba).range ≃* ↥(zpowers a ⊔ zpowers b) :=
    MulEquiv.subgroupCongr (sec11D8Hom_range ha4 hb2 hba)
  exact ⟨(e1.trans e2).symm⟩

theorem sec11_isD8_of {t r : G} (ht : t * t = 1) (hr : r * r = 1) (h4 : (t * r) ^ 4 = 1)
    (h2 : (t * r) ^ 2 ≠ 1) : IsD8 (zpowers t ⊔ zpowers r) := by
  have hba : t * (t * r) * t = (t * r)⁻¹ := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
    rw [mul_inv_rev, htinv, hrinv, ← mul_assoc, ht, one_mul]
  have key := sec11_isD8_of_ab h4 ht hba h2
  have hsup : zpowers (t * r) ⊔ zpowers t = zpowers t ⊔ zpowers r := by
    apply le_antisymm
    · refine sup_le (zpowers_le.mpr (mul_mem (mem_sup_left (mem_zpowers t))
        (mem_sup_right (mem_zpowers r)))) (zpowers_le.mpr (mem_sup_left (mem_zpowers t)))
    · refine sup_le (zpowers_le.mpr (mem_sup_right (mem_zpowers t))) (zpowers_le.mpr ?_)
      have hr' : r = t * (t * r) := by rw [← mul_assoc, ht, one_mul]
      have hmem : t * (t * r) ∈ zpowers (t * r) ⊔ zpowers t :=
        mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (mem_zpowers (t * r)))
      rwa [← hr'] at hmem
  rw [hsup] at key
  exact key

end CFSG.OddStandard.SmallF3.Omega
