module

public import CFSG.GH74.GLS.Stage4.T2NegRU3Defs

public section

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3 Matrix

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk41RU3

variable {p n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p n K}

theorem coe_tzU (h : UnitaryFieldData p n K) :
    (((tzU h : hypSU h 1 1) : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      tzMat K := rfl

@[simp] theorem tzMat_ee : tzMat K (.inl 0) (.inl 0) = -1 := by simp [tzMat]
@[simp] theorem tzMat_ez : tzMat K (.inl 0) (.inr (.inl 0)) = 0 := by simp [tzMat]
@[simp] theorem tzMat_ef : tzMat K (.inl 0) (.inr (.inr 0)) = 0 := by simp [tzMat]
@[simp] theorem tzMat_ze : tzMat K (.inr (.inl 0)) (.inl 0) = 0 := by simp [tzMat]
@[simp] theorem tzMat_zz : tzMat K (.inr (.inl 0)) (.inr (.inl 0)) = 1 := by simp [tzMat]
@[simp] theorem tzMat_zf : tzMat K (.inr (.inl 0)) (.inr (.inr 0)) = 0 := by simp [tzMat]
@[simp] theorem tzMat_fe : tzMat K (.inr (.inr 0)) (.inl 0) = 0 := by simp [tzMat]
@[simp] theorem tzMat_fz : tzMat K (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by simp [tzMat]
@[simp] theorem tzMat_ff : tzMat K (.inr (.inr 0)) (.inr (.inr 0)) = -1 := by simp [tzMat]

theorem tzMat_mul_self : tzMat K * tzMat K = 1 := by
  refine matrix_ext_hyp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type]

@[expose] def negA (x : UHeis h) : UHeis h :=
  ⟨-x.a, x.c, by
    have := x.hc
    simp only [map_neg, neg_mul_neg]
    exact this⟩

@[simp] theorem negA_a (x : UHeis h) : (negA x).a = -x.a := rfl
@[simp] theorem negA_c (x : UHeis h) : (negA x).c = x.c := rfl

theorem tzMat_mul_uMat_mul_tzMat (x : UHeis h) :
    tzMat K * uMat x * tzMat K = uMat (negA x) := by
  refine matrix_ext_hyp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem tzU_mul_tzU (h : UnitaryFieldData p n K) : tzU h * tzU h = 1 :=
  Subtype.ext (Units.ext tzMat_mul_self)

theorem tzU_inv (h : UnitaryFieldData p n K) : (tzU h)⁻¹ = tzU h :=
  inv_eq_of_mul_eq_one_right (tzU_mul_tzU h)

theorem tzU_mul_uSU_mul_tzU (x : UHeis h) : tzU h * uSU x * tzU h = uSU (negA x) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_tzU, coe_uSU]
  exact tzMat_mul_uMat_mul_tzMat x

theorem two_ne_zero_of_ne (hp2 : p ≠ 2) (h : UnitaryFieldData p n K) : (2 : K) ≠ 0 := by
  have : CharP K p := h.charP
  exact Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)

theorem tzU_ne_one (hp2 : p ≠ 2) (h : UnitaryFieldData p n K) : tzU h ≠ 1 := by
  intro h1
  have h2 := two_ne_zero_of_ne hp2 h
  have := congrArg (fun g : hypSU h 1 1 =>
    ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl 0) (.inl 0)) h1
  simp [coe_tzU] at this
  apply h2
  linear_combination -this

theorem orderOf_tzU (hp2 : p ≠ 2) (h : UnitaryFieldData p n K) : orderOf (tzU h) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact tzU_mul_tzU h) (tzU_ne_one hp2 h)

theorem mem_X0U {g : hypSU h 1 1} : g ∈ X0U h ↔ ∃ x : UHeis h, x.a = 0 ∧ uSU x = g := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, UHeis.mem_center.mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, UHeis.mem_center.mpr hx, rfl⟩

theorem card_X0U (h : UnitaryFieldData p n K) : Nat.card (X0U h) = p ^ n := by
  rw [X0U, Subgroup.card_map_of_injective uSU_injective, UHeis.card_center h]

theorem X0U_le_unitriangular : X0U h ≤ hypUnitriangular h 1 1 := by
  rintro _ ⟨x, -, rfl⟩
  exact uSU_mem x

theorem X0U_le_centralizer_tz : X0U h ≤ Subgroup.centralizer ({tzU h} : Set (hypSU h 1 1)) := by
  intro g hg
  obtain ⟨y, hy, rfl⟩ := mem_X0U.mp hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  symm
  have e := tzU_mul_uSU_mul_tzU y
  have hneg : negA y = y := UHeis.ext (by simp [hy]) rfl
  rw [hneg] at e
  calc tzU h * uSU y = tzU h * uSU y * (tzU h * tzU h) := by rw [tzU_mul_tzU, mul_one]
    _ = (tzU h * uSU y * tzU h) * tzU h := by simp only [mul_assoc]
    _ = uSU y * tzU h := by rw [e]

theorem tzU_conj_mul (x : UHeis h) :
    tzU h * uSU x * (tzU h)⁻¹ * uSU x = uSU (negA x * x) := by
  rw [tzU_inv, tzU_mul_uSU_mul_tzU, map_mul]

theorem negA_mul_mem_center (x : UHeis h) : negA x * x ∈ Subgroup.center (UHeis h) :=
  UHeis.mem_center.mpr (by simp)

end CFSG.GH74.GLS.IVK.Proofs2.Ivk41RU3
