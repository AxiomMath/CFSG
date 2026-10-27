module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.ComponentClassification.HSFLit

open Subgroup

theorem exists_mulEquiv_prod {G M N : Type*} [Group G] [Group M] [Group N] [Finite G]
    {A B : Subgroup G} (hAB : A ⊓ B = ⊥) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hcard : Nat.card A * Nat.card B = Nat.card G) (eA : A ≃* M) (eB : B ≃* N) :
    ∃ φ : G ≃* M × N, (∀ a : A, φ a = (eA a, 1)) ∧ (∀ b : B, φ b = (1, eB b)) := by
  set f : M × N →* G :=
    (A.subtype.comp eA.symm.toMonoidHom).noncommCoprod (B.subtype.comp eB.symm.toMonoidHom)
      (fun p q => hcomm _ (eA.symm p).2 _ (eB.symm q).2) with hf
  have hfapp : ∀ p q, f (p, q) = (eA.symm p : G) * (eB.symm q : G) := fun _ _ => rfl
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨p, q⟩ hpq
    rw [MonoidHom.mem_ker, hfapp] at hpq
    have hmem : (eA.symm p : G) ∈ A ⊓ B := by
      refine Subgroup.mem_inf.mpr ⟨(eA.symm p).2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hpq]
      exact inv_mem (eB.symm q).2
    rw [hAB, mem_bot] at hmem
    have hp : p = 1 := by
      have : eA.symm p = 1 := Subtype.ext hmem
      simpa using congrArg eA this
    rw [hmem, one_mul] at hpq
    have hq : q = 1 := by
      have : eB.symm q = 1 := Subtype.ext hpq
      simpa using congrArg eB this
    rw [hp, hq]
    exact one_mem _
  have : Finite (M × N) := by
    have : Finite M := Finite.of_equiv _ eA.toEquiv
    have : Finite N := Finite.of_equiv _ eB.toEquiv
    infer_instance
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [← hcard, Nat.card_prod, Nat.card_congr eA.toEquiv, Nat.card_congr eB.toEquiv]
  set e := MulEquiv.ofBijective f hbij
  refine ⟨e.symm, fun a => ?_, fun b => ?_⟩
  · rw [MulEquiv.symm_apply_eq]
    change (a : G) = f (eA a, 1)
    rw [hfapp]
    simp
  · rw [MulEquiv.symm_apply_eq]
    change (b : G) = f (1, eB b)
    rw [hfapp]
    simp

variable {G : Type*} [Group G]

@[expose] def dihedralLift (n : ℕ) [NeZero n] (a b : G) (ha : a ^ n = 1) (hb : b * b = 1)
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

theorem dihedralLift_r (n : ℕ) [NeZero n] (a b : G) (ha : a ^ n = 1) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (i : ZMod n) :
    dihedralLift n a b ha hb hba (DihedralGroup.r i) = a ^ i.val := rfl

theorem dihedralLift_sr (n : ℕ) [NeZero n] (a b : G) (ha : a ^ n = 1) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (i : ZMod n) :
    dihedralLift n a b ha hb hba (DihedralGroup.sr i) = b * a ^ i.val := rfl

theorem injective_dihedralLift (n : ℕ) [NeZero n] (a b : G) (ha : a ^ n = 1) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (hao : orderOf a = n) (hbn : b ∉ zpowers a) :
    Function.Injective (dihedralLift n a b ha hb hba) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro (i | i) hi <;> rw [MonoidHom.mem_ker] at hi
  · rw [dihedralLift_r] at hi
    have h1 : orderOf a ∣ i.val := orderOf_dvd_of_pow_eq_one hi
    rw [hao] at h1
    have h2 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt i)
    rw [ZMod.val_eq_zero] at h2
    rw [h2]
    exact one_mem _
  · exfalso
    rw [dihedralLift_sr] at hi
    apply hbn
    rw [eq_inv_of_mul_eq_one_left hi]
    exact inv_mem (pow_mem (mem_zpowers a) _)

theorem range_dihedralLift (n : ℕ) [NeZero n] (a b : G) (ha : a ^ n = 1) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) :
    (dihedralLift n a b ha hb hba).range = zpowers a ⊔ zpowers b := by
  apply le_antisymm
  · rintro _ ⟨i | i, rfl⟩
    · rw [dihedralLift_r]
      exact mem_sup_left (pow_mem (mem_zpowers a) _)
    · rw [dihedralLift_sr]
      exact mul_mem (mem_sup_right (mem_zpowers b)) (mem_sup_left (pow_mem (mem_zpowers a) _))
  · refine sup_le ?_ ?_ <;> rw [zpowers_le]
    · refine ⟨DihedralGroup.r 1, ?_⟩
      rw [dihedralLift_r]
      rcases Nat.lt_or_ge 1 n with h | h
      · rw [ZMod.val_one'' (by omega), pow_one]
      · have hn : n = 1 := by have := NeZero.ne n; omega
        subst hn
        rw [pow_one] at ha
        simp [ha]
    · refine ⟨DihedralGroup.sr 0, ?_⟩
      rw [dihedralLift_sr, ZMod.val_zero, pow_zero, mul_one]

end CFSG.ComponentClassification.HSFLit
