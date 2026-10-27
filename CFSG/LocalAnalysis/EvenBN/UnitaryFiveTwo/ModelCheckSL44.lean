module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow

open Matrix CFSG.Fischer
open scoped MatrixGroups

@[expose] def pMat (a₁ a₂ a₃ a₄ a₅ a₈ : F4) : Matrix (Fin 4) (Fin 4) F4 :=
  !![1, 0, 0, 0; a₁, 1, 0, 0; a₄, a₂, 1, 0; a₈, a₅, a₃, 1]

theorem det_pMat (a₁ a₂ a₃ a₄ a₅ a₈ : F4) : (pMat a₁ a₂ a₃ a₄ a₅ a₈).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [pMat, Fin.prod_univ_four]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pMat, OrderDual.toDual_lt_toDual] <;> contradiction

@[expose] def pSL (a₁ a₂ a₃ a₄ a₅ a₈ : F4) : SL(4, F4) :=
  ⟨pMat a₁ a₂ a₃ a₄ a₅ a₈, det_pMat a₁ a₂ a₃ a₄ a₅ a₈⟩

@[simp] theorem coe_pSL (a₁ a₂ a₃ a₄ a₅ a₈ : F4) :
    (pSL a₁ a₂ a₃ a₄ a₅ a₈ : Matrix (Fin 4) (Fin 4) F4) = pMat a₁ a₂ a₃ a₄ a₅ a₈ :=
  rfl

theorem pSL_apply (a₁ a₂ a₃ a₄ a₅ a₈ : F4) :
    pSL a₁ a₂ a₃ a₄ a₅ a₈ 1 0 = a₁ ∧ pSL a₁ a₂ a₃ a₄ a₅ a₈ 2 1 = a₂ ∧
      pSL a₁ a₂ a₃ a₄ a₅ a₈ 3 2 = a₃ ∧ pSL a₁ a₂ a₃ a₄ a₅ a₈ 2 0 = a₄ ∧
      pSL a₁ a₂ a₃ a₄ a₅ a₈ 3 1 = a₅ ∧ pSL a₁ a₂ a₃ a₄ a₅ a₈ 3 0 = a₈ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pSL_eq_pSL_iff {a₁ a₂ a₃ a₄ a₅ a₈ b₁ b₂ b₃ b₄ b₅ b₈ : F4} :
    pSL a₁ a₂ a₃ a₄ a₅ a₈ = pSL b₁ b₂ b₃ b₄ b₅ b₈ ↔
      a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ ∧ a₄ = b₄ ∧ a₅ = b₅ ∧ a₈ = b₈ := by
  constructor
  · intro h
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₈⟩ := pSL_apply a₁ a₂ a₃ a₄ a₅ a₈
    rw [h] at e₁ e₂ e₃ e₄ e₅ e₈
    obtain ⟨f₁, f₂, f₃, f₄, f₅, f₈⟩ := pSL_apply b₁ b₂ b₃ b₄ b₅ b₈
    exact ⟨e₁.symm.trans f₁, e₂.symm.trans f₂, e₃.symm.trans f₃, e₄.symm.trans f₄,
      e₅.symm.trans f₅, e₈.symm.trans f₈⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

theorem pSL_zero : pSL 0 0 0 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pSL_mul (a₁ a₂ a₃ a₄ a₅ a₈ b₁ b₂ b₃ b₄ b₅ b₈ : F4) :
    pSL a₁ a₂ a₃ a₄ a₅ a₈ * pSL b₁ b₂ b₃ b₄ b₅ b₈ =
      pSL (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + a₂ * b₁ + b₄) (a₅ + a₃ * b₂ + b₅)
        (a₈ + a₅ * b₁ + a₃ * b₄ + b₈) := by
  ext i j
  simp only [coe_pSL]
  fin_cases i <;> fin_cases j <;> simp [pMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem pSL_inv (a₁ a₂ a₃ a₄ a₅ a₈ : F4) :
    (pSL a₁ a₂ a₃ a₄ a₅ a₈)⁻¹ = pSL a₁ a₂ a₃ (a₄ + a₂ * a₁) (a₅ + a₃ * a₂)
      (a₈ + a₅ * a₁ + a₃ * a₄ + a₃ * a₂ * a₁) := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [pSL_mul, ← pSL_zero, pSL_eq_pSL_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination a₁ * F4.two_eq_zero
  · linear_combination a₂ * F4.two_eq_zero
  · linear_combination a₃ * F4.two_eq_zero
  · linear_combination (a₄ + a₂ * a₁) * F4.two_eq_zero
  · linear_combination (a₅ + a₃ * a₂) * F4.two_eq_zero
  · linear_combination (a₈ + a₅ * a₁ + a₃ * a₄ + a₃ * a₂ * a₁) * F4.two_eq_zero

theorem pSL_mul_self (a₁ a₂ a₃ a₄ a₅ a₈ : F4) :
    pSL a₁ a₂ a₃ a₄ a₅ a₈ * pSL a₁ a₂ a₃ a₄ a₅ a₈ =
      pSL 0 0 0 (a₂ * a₁) (a₃ * a₂) (a₅ * a₁ + a₃ * a₄) := by
  rw [pSL_mul, pSL_eq_pSL_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination a₁ * F4.two_eq_zero
  · linear_combination a₂ * F4.two_eq_zero
  · linear_combination a₃ * F4.two_eq_zero
  · linear_combination a₄ * F4.two_eq_zero
  · linear_combination a₅ * F4.two_eq_zero
  · linear_combination a₈ * F4.two_eq_zero

theorem pSL_mul_self_eq_one_iff {a₁ a₂ a₃ a₄ a₅ a₈ : F4} :
    pSL a₁ a₂ a₃ a₄ a₅ a₈ * pSL a₁ a₂ a₃ a₄ a₅ a₈ = 1 ↔
      a₂ * a₁ = 0 ∧ a₃ * a₂ = 0 ∧ a₅ * a₁ + a₃ * a₄ = 0 := by
  rw [pSL_mul_self, ← pSL_zero, pSL_eq_pSL_iff]
  simp

theorem pSL_mul_comm_iff {a₁ a₂ a₃ a₄ a₅ a₈ b₁ b₂ b₃ b₄ b₅ b₈ : F4} :
    pSL a₁ a₂ a₃ a₄ a₅ a₈ * pSL b₁ b₂ b₃ b₄ b₅ b₈ = pSL b₁ b₂ b₃ b₄ b₅ b₈ * pSL a₁ a₂ a₃ a₄ a₅ a₈ ↔
      a₂ * b₁ = b₂ * a₁ ∧ a₃ * b₂ = b₃ * a₂ ∧ a₅ * b₁ + a₃ * b₄ = b₅ * a₁ + b₃ * a₄ := by
  rw [pSL_mul, pSL_mul, pSL_eq_pSL_iff]
  constructor
  · rintro ⟨-, -, -, h₄, h₅, h₈⟩
    exact ⟨by linear_combination h₄, by linear_combination h₅, by linear_combination h₈⟩
  · rintro ⟨h₄, h₅, h₈⟩
    exact ⟨add_comm _ _, add_comm _ _, add_comm _ _, by linear_combination h₄,
      by linear_combination h₅, by linear_combination h₈⟩

theorem mSL_mul_self_eq_one_iff {a b c d z : F4} :
    pSL a 0 d b c z * pSL a 0 d b c z = 1 ↔ c * a + d * b = 0 := by
  rw [pSL_mul_self_eq_one_iff]
  simp

theorem mSL_mul_comm_iff {a b c d z a' b' c' d' z' : F4} :
    pSL a 0 d b c z * pSL a' 0 d' b' c' z' = pSL a' 0 d' b' c' z' * pSL a 0 d b c z ↔
      c * a' + d * b' = c' * a + d' * b := by
  rw [pSL_mul_comm_iff]
  simp

@[expose] def PK : Subgroup SL(4, F4) where
  carrier := {x | ∃ a₁ a₂ a₃ a₄ a₅ a₈, x = pSL a₁ a₂ a₃ a₄ a₅ a₈}
  mul_mem' := by
    rintro _ _ ⟨a₁, a₂, a₃, a₄, a₅, a₈, rfl⟩ ⟨b₁, b₂, b₃, b₄, b₅, b₈, rfl⟩
    exact ⟨_, _, _, _, _, _, pSL_mul _ _ _ _ _ _ _ _ _ _ _ _⟩
  one_mem' := ⟨0, 0, 0, 0, 0, 0, pSL_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a₁, a₂, a₃, a₄, a₅, a₈, rfl⟩
    exact ⟨_, _, _, _, _, _, pSL_inv _ _ _ _ _ _⟩

theorem pSL_mem_PK (a₁ a₂ a₃ a₄ a₅ a₈ : F4) : pSL a₁ a₂ a₃ a₄ a₅ a₈ ∈ PK :=
  ⟨_, _, _, _, _, _, rfl⟩

theorem eq_pSL_of_mem_PK {x : SL(4, F4)} (hx : x ∈ PK) :
    x = pSL (x 1 0) (x 2 1) (x 3 2) (x 2 0) (x 3 1) (x 3 0) := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₈, rfl⟩ := hx
  rfl

@[expose] def YK : Subgroup SL(4, F4) where
  carrier := {x | ∃ a₂ a₄ a₅ a₈, x = pSL 0 a₂ 0 a₄ a₅ a₈}
  mul_mem' := by
    rintro _ _ ⟨a₂, a₄, a₅, a₈, rfl⟩ ⟨b₂, b₄, b₅, b₈, rfl⟩
    exact ⟨a₂ + b₂, a₄ + b₄, a₅ + b₅, a₈ + b₈, by rw [pSL_mul]; simp⟩
  one_mem' := ⟨0, 0, 0, 0, pSL_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a₂, a₄, a₅, a₈, rfl⟩
    exact ⟨a₂, a₄, a₅, a₈, by rw [pSL_inv]; simp⟩

theorem YK_le_PK : YK ≤ PK := by
  rintro _ ⟨a₂, a₄, a₅, a₈, rfl⟩
  exact pSL_mem_PK _ _ _ _ _ _

@[expose] def mSub (p : F4 → F4 → F4 → F4 → Prop) (h0 : p 0 0 0 0)
    (hadd : ∀ {a b c d a' b' c' d' : F4}, p a b c d → p a' b' c' d' →
      p (a + a') (b + b') (c + c') (d + d')) : Subgroup SL(4, F4) where
  carrier := {x | ∃ a b c d z, p a b c d ∧ x = pSL a 0 d b c z}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, d, z, h, rfl⟩ ⟨a', b', c', d', z', h', rfl⟩
    exact ⟨a + a', b + b', c + c', d + d', z + c * a' + d * b' + z', hadd h h',
      by rw [pSL_mul]; simp⟩
  one_mem' := ⟨0, 0, 0, 0, 0, h0, pSL_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, d, z, h, rfl⟩
    exact ⟨a, b, c, d, z + c * a + d * b, h, by rw [pSL_inv]; simp⟩

@[expose] def MK : Subgroup SL(4, F4) :=
  mSub (fun _ _ _ _ => True) trivial fun _ _ => trivial

theorem mem_MK {x : SL(4, F4)} : x ∈ MK ↔ ∃ a b c d z, x = pSL a 0 d b c z := by
  change (∃ a b c d z, True ∧ _) ↔ _
  simp

theorem eq_pSL_of_mem_MK {x : SL(4, F4)} (hx : x ∈ MK) :
    x = pSL (x 1 0) 0 (x 3 2) (x 2 0) (x 3 1) (x 3 0) := by
  obtain ⟨a, b, c, d, z, rfl⟩ := mem_MK.1 hx
  rfl

theorem mem_mSub {p : F4 → F4 → F4 → F4 → Prop} {h0 hadd} {x : SL(4, F4)} :
    x ∈ mSub p h0 hadd ↔ x ∈ MK ∧ p (x 1 0) (x 2 0) (x 3 1) (x 3 2) := by
  constructor
  · rintro ⟨a, b, c, d, z, h, rfl⟩
    exact ⟨mem_MK.2 ⟨a, b, c, d, z, rfl⟩, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨_, _, _, _, _, h, eq_pSL_of_mem_MK hx⟩

theorem pSL_mem_mSub {p : F4 → F4 → F4 → F4 → Prop} {h0 hadd} {a b c d z : F4}
    (h : p a b c d) : pSL a 0 d b c z ∈ mSub p h0 hadd :=
  ⟨a, b, c, d, z, h, rfl⟩

@[expose] def ZK : Subgroup SL(4, F4) :=
  mSub (fun a b c d => a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ⟨rfl, rfl, rfl, rfl⟩
    fun ⟨ha, hb, hc, hd⟩ ⟨ha', hb', hc', hd'⟩ => by simp [ha, hb, hc, hd, ha', hb', hc', hd']

@[expose] def Z₂K : Subgroup SL(4, F4) :=
  mSub (fun a _ _ d => a = 0 ∧ d = 0) ⟨rfl, rfl⟩
    fun ⟨ha, hd⟩ ⟨ha', hd'⟩ => by simp [ha, hd, ha', hd']

@[expose] def B₁K : Subgroup SL(4, F4) :=
  mSub (fun _ _ c d => c = 0 ∧ d = 0) ⟨rfl, rfl⟩
    fun ⟨hc, hd⟩ ⟨hc', hd'⟩ => by simp [hc, hd, hc', hd']

@[expose] def B₂K : Subgroup SL(4, F4) :=
  mSub (fun a b _ _ => a = 0 ∧ b = 0) ⟨rfl, rfl⟩
    fun ⟨ha, hb⟩ ⟨ha', hb'⟩ => by simp [ha, hb, ha', hb']

@[expose] def UK (l : F4) : Subgroup SL(4, F4) :=
  mSub (fun a b c d => d = l * a ∧ c = l * b) ⟨(mul_zero l).symm, (mul_zero l).symm⟩
    fun ⟨hd, hc⟩ ⟨hd', hc'⟩ => by rw [hd, hc, hd', hc', mul_add, mul_add]; exact ⟨rfl, rfl⟩

@[expose] def Z₂Line (p q : F4) : Subgroup SL(4, F4) :=
  mSub (fun a b c d => a * q = b * p ∧ c * p + d * q = 0) ⟨by simp, by simp⟩
    fun ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ => ⟨by linear_combination h₁ + h₁', by linear_combination h₂ + h₂'⟩

theorem card_eq_of_range {T : Type} [Finite T] {H : Subgroup SL(4, F4)} (f : T → SL(4, F4))
    (hf : Function.Injective f) (hH : Set.range f = H) : Nat.card H = Nat.card T := by
  rw [← Nat.card_range_of_injective hf, hH]
  rfl

theorem card_PK : Nat.card PK = 2 ^ 12 := by
  rw [card_eq_of_range (T := F4 × F4 × F4 × F4 × F4 × F4)
    (fun a => pSL a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2)]
  · simp [Nat.card_eq_fintype_card, F4.card]
  · rintro ⟨a₁, a₂, a₃, a₄, a₅, a₈⟩ ⟨b₁, b₂, b₃, b₄, b₅, b₈⟩ h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := pSL_eq_pSL_iff.1 h
    rfl
  · ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact pSL_mem_PK _ _ _ _ _ _
    · rintro ⟨a₁, a₂, a₃, a₄, a₅, a₈, rfl⟩
      exact ⟨(a₁, a₂, a₃, a₄, a₅, a₈), rfl⟩

theorem card_YK : Nat.card YK = 2 ^ 8 := by
  rw [card_eq_of_range (T := F4 × F4 × F4 × F4) (fun a => pSL 0 a.1 0 a.2.1 a.2.2.1 a.2.2.2)]
  · simp [Nat.card_eq_fintype_card, F4.card]
  · rintro ⟨a₂, a₄, a₅, a₈⟩ ⟨b₂, b₄, b₅, b₈⟩ h
    obtain ⟨-, rfl, -, rfl, rfl, rfl⟩ := pSL_eq_pSL_iff.1 h
    rfl
  · ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, _, _, _, rfl⟩
    · rintro ⟨a₂, a₄, a₅, a₈, rfl⟩
      exact ⟨(a₂, a₄, a₅, a₈), rfl⟩

theorem card_mSub {p : F4 → F4 → F4 → F4 → Prop} {h0 hadd}
    [DecidablePred fun q : F4 × F4 × F4 × F4 => p q.1 q.2.1 q.2.2.1 q.2.2.2] :
    Nat.card (mSub p h0 hadd) =
      Fintype.card {q : F4 × F4 × F4 × F4 // p q.1 q.2.1 q.2.2.1 q.2.2.2} * 4 := by
  rw [card_eq_of_range (T := {q : F4 × F4 × F4 × F4 // p q.1 q.2.1 q.2.2.1 q.2.2.2} × F4)
    (fun q => pSL q.1.1.1 0 q.1.1.2.2.2 q.1.1.2.1 q.1.1.2.2.1 q.2)]
  · rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := F4), F4.card]
  · rintro ⟨⟨⟨a, b, c, d⟩, hq⟩, z⟩ ⟨⟨⟨a', b', c', d'⟩, hq'⟩, z'⟩ h
    obtain ⟨rfl, -, rfl, rfl, rfl, rfl⟩ := pSL_eq_pSL_iff.1 h
    rfl
  · ext x
    constructor
    · rintro ⟨⟨⟨⟨a, b, c, d⟩, h⟩, z⟩, rfl⟩
      exact ⟨a, b, c, d, z, h, rfl⟩
    · rintro ⟨a, b, c, d, z, h, rfl⟩
      exact ⟨(⟨(a, b, c, d), h⟩, z), rfl⟩

theorem card_ZK : Nat.card ZK = 4 := by
  rw [ZK, card_mSub]
  decide +kernel

theorem card_Z₂K : Nat.card Z₂K = 2 ^ 6 := by
  rw [Z₂K, card_mSub]
  decide +kernel

theorem card_B₁K : Nat.card B₁K = 2 ^ 6 := by
  rw [B₁K, card_mSub]
  decide +kernel

theorem card_B₂K : Nat.card B₂K = 2 ^ 6 := by
  rw [B₂K, card_mSub]
  decide +kernel

theorem card_UK (l : F4) : Nat.card (UK l) = 2 ^ 6 := by
  rw [UK, card_mSub]
  revert l
  decide +kernel

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow
