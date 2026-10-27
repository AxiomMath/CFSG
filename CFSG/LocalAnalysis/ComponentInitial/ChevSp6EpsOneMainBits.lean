module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillFacts
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Matrix

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def enc3 (w : Fin 3 → ZMod 2) : ℕ := (w 0).val + 2 * (w 1).val + 4 * (w 2).val

@[expose] def dec3 (n : ℕ) : Fin 3 → ZMod 2 :=
  ![((n % 2 : ℕ) : ZMod 2), ((n / 2 % 2 : ℕ) : ZMod 2), ((n / 4 % 2 : ℕ) : ZMod 2)]

theorem eta3 (w : Fin 3 → ZMod 2) : w = ![w 0, w 1, w 2] := by
  ext i
  fin_cases i <;> rfl

theorem forall_vec3 {Q : (Fin 3 → ZMod 2) → Prop} (h : ∀ a b c : ZMod 2, Q ![a, b, c])
    (w : Fin 3 → ZMod 2) : Q w := by
  rw [eta3 w]
  exact h _ _ _

theorem enc3_lt (w : Fin 3 → ZMod 2) : enc3 w < 8 :=
  forall_vec3 (Q := fun w => enc3 w < 8) (by decide) w

theorem enc3_add (w w' : Fin 3 → ZMod 2) : enc3 (w + w') = enc3 w ^^^ enc3 w' := by
  have key : ∀ a b c a' b' c' : ZMod 2,
      enc3 (![a, b, c] + ![a', b', c']) = enc3 ![a, b, c] ^^^ enc3 ![a', b', c'] := by
    decide
  rw [eta3 w, eta3 w']
  exact key _ _ _ _ _ _

theorem enc3_eq_zero (w : Fin 3 → ZMod 2) : enc3 w = 0 ↔ w = 0 :=
  forall_vec3 (Q := fun w => enc3 w = 0 ↔ w = 0) (by decide) w

theorem enc3_dec3 {n : ℕ} (hn : n < 8) : enc3 (dec3 n) = n := by
  interval_cases n <;> rfl

theorem mkv_xor : ∀ a, a < 8 → ∀ b, b < 8 → ∀ a', a' < 8 → ∀ b', b' < 8 →
    mkv (a ^^^ a') (b ^^^ b') = mkv a b ^^^ mkv a' b' := by
  decide +kernel

theorem mkv_lt : ∀ a, a < 8 → ∀ b, b < 8 → mkv a b < 64 := by decide +kernel

theorem mkv_eq_zero : ∀ a, a < 8 → ∀ b, b < 8 → (mkv a b = 0 ↔ a = 0 ∧ b = 0) := by
  decide +kernel

theorem mkv_parts : ∀ v, v < 64 → wpart v < 8 ∧ xpart v < 8 ∧ mkv (wpart v) (xpart v) = v := by
  decide +kernel

@[expose] def enc6 (p : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : ℕ := mkv (enc3 p.1) (enc3 p.2)

theorem enc6_lt (p : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : enc6 p < 64 :=
  mkv_lt _ (enc3_lt _) _ (enc3_lt _)

theorem enc6_add (p p' : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) :
    enc6 (p + p') = enc6 p ^^^ enc6 p' := by
  rw [enc6, enc6, enc6, Prod.fst_add, Prod.snd_add, enc3_add, enc3_add]
  exact mkv_xor _ (enc3_lt _) _ (enc3_lt _) _ (enc3_lt _) _ (enc3_lt _)

theorem enc6_eq_zero (p : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : enc6 p = 0 ↔ p = 0 := by
  rw [enc6, mkv_eq_zero _ (enc3_lt _) _ (enc3_lt _), enc3_eq_zero, enc3_eq_zero, Prod.ext_iff]
  rfl

theorem enc6_surj {v : ℕ} (hv : v < 64) : enc6 (dec3 (wpart v), dec3 (xpart v)) = v := by
  obtain ⟨hw, hx, he⟩ := mkv_parts v hv
  rw [enc6, enc3_dec3 hw, enc3_dec3 hx, he]

@[expose] def enc9 (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : ℕ :=
  8 * (8 * enc3 (B 2) + enc3 (B 1)) + enc3 (B 0)

@[expose] def dec9 (n : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of ![dec3 (n % 8), dec3 (n / 8 % 8), dec3 (n / 64)]

theorem xor_pack {a a' : ℕ} (ha : a < 8) (ha' : a' < 8) (b b' : ℕ) :
    (8 * b + a) ^^^ (8 * b' + a') = 8 * (b ^^^ b') + (a ^^^ a') := by
  have h8 : (8 : ℕ) = 2 ^ 3 := rfl
  have hx : a ^^^ a' < 2 ^ 3 := Nat.xor_lt_two_pow (n := 3) ha ha'
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, h8, Nat.testBit_two_pow_mul_add _ (h8 ▸ ha),
    Nat.testBit_two_pow_mul_add _ (h8 ▸ ha'), Nat.testBit_two_pow_mul_add _ hx,
    Nat.testBit_xor, Nat.testBit_xor]
  split_ifs <;> rfl

theorem enc9_lt (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : enc9 B < 512 := by
  have h0 := enc3_lt (B 0)
  have h1 := enc3_lt (B 1)
  have h2 := enc3_lt (B 2)
  unfold enc9
  omega

theorem enc9_add (B B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    enc9 (B + B') = enc9 B ^^^ enc9 B' := by
  have hrow : ∀ i, (B + B') i = B i + B' i := fun i => rfl
  have hlt : ∀ (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i : Fin 3), enc3 (M i) < 8 :=
    fun M i => enc3_lt _
  unfold enc9
  rw [hrow, hrow, hrow, enc3_add, enc3_add, enc3_add,
    xor_pack (hlt B 0) (hlt B' 0), xor_pack (hlt B 1) (hlt B' 1)]

theorem enc9_eq_zero (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : enc9 B = 0 ↔ B = 0 := by
  constructor
  · intro h
    unfold enc9 at h
    have h0 : enc3 (B 0) = 0 := by omega
    have h1 : enc3 (B 1) = 0 := by omega
    have h2 : enc3 (B 2) = 0 := by omega
    rw [enc3_eq_zero] at h0 h1 h2
    ext i j
    fin_cases i
    · exact congrFun h0 j
    · exact congrFun h1 j
    · exact congrFun h2 j
  · rintro rfl
    rfl

theorem enc9_surj {n : ℕ} (hn : n < 512) : enc9 (dec9 n) = n := by
  have e0 : enc3 (dec9 n 0) = n % 8 := enc3_dec3 (Nat.mod_lt _ (by norm_num))
  have e1 : enc3 (dec9 n 1) = n / 8 % 8 := enc3_dec3 (Nat.mod_lt _ (by norm_num))
  have e2 : enc3 (dec9 n 2) = n / 64 := enc3_dec3 (by omega)
  unfold enc9
  rw [e0, e1, e2]
  omega

theorem forall_vec6 {Q : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → Prop}
    (h : ∀ a b c a' b' c' : ZMod 2, Q ![a, b, c] ![a', b', c']) (w x : Fin 3 → ZMod 2) :
    Q w x := by
  rw [eta3 w, eta3 x]
  exact h _ _ _ _ _ _

@[expose] def qMat (u : Bool) (w x : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  vecMulVec w w + vecMulVec w x + if u then vecMulVec x x else 0

theorem qOf_enc6 (u : Bool) (w x : Fin 3 → ZMod 2) : qOf u (enc6 (w, x)) = enc9 (qMat u w x) := by
  have key : ∀ a b c a' b' c' : ZMod 2,
      qOf u (enc6 (![a, b, c], ![a', b', c'])) = enc9 (qMat u ![a, b, c] ![a', b', c']) := by
    cases u <;> decide
  exact forall_vec6 (Q := fun w x => qOf u (enc6 (w, x)) = enc9 (qMat u w x)) key w x

theorem z0T_enc6 (w x : Fin 3 → ZMod 2) : evalV z0T (enc6 (w, x)) = enc6 (w + x, x) := by
  have key : ∀ a b c a' b' c' : ZMod 2,
      evalV z0T (enc6 (![a, b, c], ![a', b', c'])) =
        enc6 (![a, b, c] + ![a', b', c'], ![a', b', c']) := by
    decide
  exact forall_vec6 (Q := fun w x => evalV z0T (enc6 (w, x)) = enc6 (w + x, x)) key w x

@[expose] def mat₁ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def mat₂ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def mat₂' : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def g₁ : GL (Fin 3) (ZMod 2) := ⟨mat₁, mat₁, by decide, by decide⟩

@[expose] def g₂ : GL (Fin 3) (ZMod 2) := ⟨mat₂, mat₂', by decide, by decide⟩

theorem lam1T_enc6 (w x : Fin 3 → ZMod 2) :
    evalV lam1T (enc6 (w, x)) = enc6 ((g₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w,
      (g₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x) := by
  have key : ∀ a b c a' b' c' : ZMod 2,
      evalV lam1T (enc6 (![a, b, c], ![a', b', c'])) =
        enc6 (mat₁ *ᵥ ![a, b, c], mat₁ *ᵥ ![a', b', c']) := by
    decide
  exact forall_vec6 (Q := fun w x => evalV lam1T (enc6 (w, x)) = enc6 (mat₁ *ᵥ w, mat₁ *ᵥ x))
    key w x

theorem lam2T_enc6 (w x : Fin 3 → ZMod 2) :
    evalV lam2T (enc6 (w, x)) = enc6 ((g₂ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w,
      (g₂ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x) := by
  have key : ∀ a b c a' b' c' : ZMod 2,
      evalV lam2T (enc6 (![a, b, c], ![a', b', c'])) =
        enc6 (mat₂ *ᵥ ![a, b, c], mat₂ *ᵥ ![a', b', c']) := by
    decide
  exact forall_vec6 (Q := fun w x => evalV lam2T (enc6 (w, x)) = enc6 (mat₂ *ᵥ w, mat₂ *ᵥ x))
    key w x

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
