module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS

variable {G : Type} [Group G]

@[expose] def dihLift (n : ℕ) [NeZero n] (a b : G) (ha : a ^ n = 1) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) : DihedralGroup n →* G where
  toFun x := match x with
    | DihedralGroup.r i => a ^ i.val
    | DihedralGroup.sr i => b * a ^ i.val
  map_one' := by
    show a ^ (0 : ZMod n).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    have hA : ∀ i j : ZMod n, a ^ i.val * a ^ j.val = a ^ (i + j).val := fun i j => by
      rw [← pow_add, pow_eq_pow_mod (i.val + j.val) ha, ← ZMod.val_add]
    have hB : ∀ i j : ZMod n, a ^ (j - i).val = (a ^ i.val)⁻¹ * a ^ j.val := fun i j => by
      apply eq_inv_mul_of_mul_eq
      rw [hA, add_sub_cancel]
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    have hC : ∀ k : ℕ, a ^ k * b = b * (a ^ k)⁻¹ := fun k => by
      have h1 : b * a ^ k * b⁻¹ = (a ^ k)⁻¹ := by rw [← conj_pow, hba, inv_pow]
      calc a ^ k * b = b * (b⁻¹ * a ^ k * b) := by group
        _ = b * (b * a ^ k * b⁻¹) := by rw [hbinv]
        _ = b * (a ^ k)⁻¹ := by rw [h1]
    rintro (i | j) (k | l)
    · show a ^ (i + k).val = a ^ i.val * a ^ k.val
      rw [hA]
    · show b * a ^ (l - i).val = a ^ i.val * (b * a ^ l.val)
      rw [hB, ← mul_assoc (a ^ i.val) b, hC, mul_assoc]
    · show b * a ^ (j + k).val = b * a ^ j.val * a ^ k.val
      rw [mul_assoc, hA]
    · show a ^ (l - j).val = b * a ^ j.val * (b * a ^ l.val)
      rw [hB, mul_assoc, ← mul_assoc (a ^ j.val), hC, mul_assoc b, ← mul_assoc b, hb, one_mul]

theorem dihLift_r (n : ℕ) [NeZero n] (a b : G) (ha : a ^ n = 1) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (i : ZMod n) :
    dihLift n a b ha hb hba (DihedralGroup.r i) = a ^ i.val := rfl

theorem dihLift_sr (n : ℕ) [NeZero n] (a b : G) (ha : a ^ n = 1) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (i : ZMod n) :
    dihLift n a b ha hb hba (DihedralGroup.sr i) = b * a ^ i.val := rfl

theorem injective_dihLift (n : ℕ) [NeZero n] (a b : G) (ha : a ^ n = 1) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (hao : orderOf a = n) (hbn : b ∉ zpowers a) :
    Function.Injective (dihLift n a b ha hb hba) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro (i | i) hi <;> rw [MonoidHom.mem_ker] at hi
  · rw [dihLift_r] at hi
    have h1 : orderOf a ∣ i.val := orderOf_dvd_of_pow_eq_one hi
    rw [hao] at h1
    have h2 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt i)
    rw [ZMod.val_eq_zero] at h2
    rw [h2]
    exact one_mem _
  · exfalso
    rw [dihLift_sr] at hi
    apply hbn
    rw [eq_inv_of_mul_eq_one_left hi]
    exact inv_mem (pow_mem (mem_zpowers a) _)

theorem range_dihLift (n : ℕ) [NeZero n] (a b : G) (ha : a ^ n = 1) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) :
    (dihLift n a b ha hb hba).range = zpowers a ⊔ zpowers b := by
  apply le_antisymm
  · rintro _ ⟨i | i, rfl⟩
    · rw [dihLift_r]
      exact mem_sup_left (pow_mem (mem_zpowers a) _)
    · rw [dihLift_sr]
      exact mul_mem (mem_sup_right (mem_zpowers b)) (mem_sup_left (pow_mem (mem_zpowers a) _))
  · refine sup_le ?_ ?_ <;> rw [zpowers_le]
    · refine ⟨DihedralGroup.r 1, ?_⟩
      rw [dihLift_r]
      rcases Nat.lt_or_ge 1 n with h | h
      · rw [ZMod.val_one'' (by omega), pow_one]
      · have hn : n = 1 := by have := NeZero.ne n; omega
        subst hn
        rw [pow_one] at ha
        simp [ha]
    · refine ⟨DihedralGroup.sr 0, ?_⟩
      rw [dihLift_sr, ZMod.val_zero, pow_zero, mul_one]

theorem exists_mulEquiv_dihedral (n : ℕ) [NeZero n] (r s : G) (hr : orderOf r = n) (hs : s * s = 1)
    (hsr : s * r * s⁻¹ = r⁻¹) (hns : s ∉ zpowers r) :
    Nonempty (↥(zpowers r ⊔ zpowers s) ≃* DihedralGroup n) := by
  have hrn : r ^ n = 1 := hr ▸ pow_orderOf_eq_one r
  let f := dihLift n r s hrn hs hsr
  have hinj : Function.Injective f := injective_dihLift n r s hrn hs hsr hr hns
  exact ⟨((MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (range_dihLift n r s hrn hs hsr))).symm⟩

theorem isDihedralTwoGroup_sup (k : ℕ) (hk : 1 ≤ k) (r s : G) (hr : orderOf r = 2 ^ k)
    (hs : s * s = 1) (hsr : s * r * s⁻¹ = r⁻¹) (hns : s ∉ zpowers r) :
    IVK.IsDihedralTwoGroup ↥(zpowers r ⊔ zpowers s) (k + 1) := by
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  refine ⟨by omega, 2 ^ k, by rw [pow_succ]; ring, ?_, ?_⟩
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  · exact exists_mulEquiv_dihedral (2 ^ k) r s hr hs hsr hns

theorem card_dihedral_sup (n : ℕ) [NeZero n] (r s : G) (hr : orderOf r = n) (hs : s * s = 1)
    (hsr : s * r * s⁻¹ = r⁻¹) (hns : s ∉ zpowers r) :
    Nat.card ↥(zpowers r ⊔ zpowers s) = 2 * n := by
  obtain ⟨e⟩ := exists_mulEquiv_dihedral n r s hr hs hsr hns
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]

theorem mem_dihedral_iff (n : ℕ) [NeZero n] {r s : G} (hrn : r ^ n = 1) (hs : s * s = 1)
    (hsr : s * r * s⁻¹ = r⁻¹) {g : G} :
    g ∈ zpowers r ⊔ zpowers s ↔ ∃ i : ℕ, g = r ^ i ∨ g = s * r ^ i := by
  constructor
  · intro hg
    rw [← range_dihLift n r s hrn hs hsr] at hg
    obtain ⟨x, rfl⟩ := hg
    rcases x with i | i
    · exact ⟨i.val, Or.inl rfl⟩
    · exact ⟨i.val, Or.inr rfl⟩
  · rintro ⟨i, rfl | rfl⟩
    · exact mem_sup_left (pow_mem (mem_zpowers r) i)
    · exact mul_mem (mem_sup_right (mem_zpowers s)) (mem_sup_left (pow_mem (mem_zpowers r) i))

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
