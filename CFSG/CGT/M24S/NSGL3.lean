module

public import CFSG.CGT.M24S.GL4

public section

namespace CFSG.CGT.M24S.NSB

open Matrix

@[expose] def v₀ : Fin 3 → ZMod 2 := ![0, 0, 1]

@[expose] def lv (c v : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) := 1 + vecMulVec c v

@[expose] def ω₀ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 1, 0; 0, 0, 1]

@[expose] def τ₀ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def ℓ₀ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

theorem exists_dotProduct_eq_one : ∀ w : Fin 3 → ZMod 2, w ≠ 0 →
    ∃ u : Fin 3 → ZMod 2, u ⬝ᵥ w = 1 := by
  decide

theorem eq_zero_or_eq_of_forall_dotProduct : ∀ c d : Fin 3 → ZMod 2, c ≠ 0 →
    (∀ f : Fin 3 → ZMod 2, f ⬝ᵥ c = 0 → f ⬝ᵥ d = 0) → d = 0 ∨ d = c := by
  decide

theorem add_ne_zero_of_ne : ∀ v w : Fin 3 → ZMod 2, v ≠ w → v + w ≠ 0 := by
  decide

set_option maxRecDepth 10000 in
theorem exists_vecMul_eq_v₀ : ∀ v : Fin 3 → ZMod 2, v ≠ 0 →
    ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B.det = 1 ∧ vecMul v B = v₀ := by
  decide

set_option maxRecDepth 10000 in
theorem exists_vecMul_v₀_eq : ∀ v : Fin 3 → ZMod 2, v ≠ 0 →
    ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B.det = 1 ∧ vecMul v₀ B = v := by
  decide

@[expose] def IsCycleFor (v w : Fin 3 → ZMod 2) : Prop :=
  ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B.det = 1 ∧ vecMul w B = v ∧ vecMul (v + w) B = w

instance (v w : Fin 3 → ZMod 2) : Decidable (IsCycleFor v w) := by
  unfold IsCycleFor
  infer_instance

set_option maxRecDepth 10000 in
theorem isCycleFor_all : ∀ v w : Fin 3 → ZMod 2, v ≠ 0 → w ≠ 0 → v ≠ w → IsCycleFor v w := by
  decide

theorem exists_cycle {v w : Fin 3 → ZMod 2} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) :
    ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B.det = 1 ∧ vecMul w B = v ∧
      vecMul (v + w) B = w :=
  isCycleFor_all v w hv hw hvw

theorem ω₀_cube : ω₀ * ω₀ * ω₀ = 1 := by decide

theorem τ₀_sq : τ₀ * τ₀ = 1 := by decide

theorem τ₀ω₀_sq : τ₀ * ω₀ * (τ₀ * ω₀) = 1 := by decide

theorem vecMul_v₀_ω₀ : vecMul v₀ ω₀ = v₀ := by decide

theorem vecMul_v₀_τ₀ : vecMul v₀ τ₀ = v₀ := by decide

theorem det_ω₀ : ω₀.det = 1 := by decide

theorem det_τ₀ : τ₀.det = 1 := by decide

@[expose] def StabDecomp (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  ∃ c : Fin 3 → ZMod 2, v₀ ⬝ᵥ c = 0 ∧ (B = lv c v₀ ∨ B = lv c v₀ * ω₀ ∨
    B = lv c v₀ * (ω₀ * ω₀) ∨ B = lv c v₀ * τ₀ ∨ B = lv c v₀ * (ω₀ * τ₀) ∨
    B = lv c v₀ * (ω₀ * ω₀ * τ₀))

instance (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Decidable (StabDecomp B) := by
  unfold StabDecomp
  infer_instance

set_option maxRecDepth 10000 in
theorem stab_decomp : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), vecMul v₀ B = v₀ → B.det ≠ 0 →
    StabDecomp B := by
  decide

@[expose] def CocycleSol (a b : Fin 3 → ZMod 2) : Prop :=
  ∃ s : Fin 3 → ZMod 2, v₀ ⬝ᵥ s = 0 ∧ a = s + ω₀ *ᵥ s ∧ b = s + τ₀ *ᵥ s

instance (a b : Fin 3 → ZMod 2) : Decidable (CocycleSol a b) := by
  unfold CocycleSol
  infer_instance

set_option maxRecDepth 10000 in
theorem cocycleSol_of : ∀ a b : Fin 3 → ZMod 2, v₀ ⬝ᵥ a = 0 → v₀ ⬝ᵥ b = 0 →
    a + ω₀ *ᵥ a + ω₀ *ᵥ (ω₀ *ᵥ a) = 0 → b + τ₀ *ᵥ b = 0 →
    (b + τ₀ *ᵥ a) + (τ₀ * ω₀) *ᵥ (b + τ₀ *ᵥ a) = 0 → CocycleSol a b := by
  decide

@[expose] def IsLv (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  ∃ k f : Fin 3 → ZMod 2, k ≠ 0 ∧ f ⬝ᵥ k = 0 ∧ B = lv k f

instance (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Decidable (IsLv B) := by
  unfold IsLv
  infer_instance

set_option maxRecDepth 10000 in
theorem isLv_of_involution : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B * B = 1 → B ≠ 1 →
    IsLv B := by
  decide

@[expose] def ConjToℓ₀ (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  ∃ P : Matrix (Fin 3) (Fin 3) (ZMod 2), P.det = 1 ∧ P * B = ℓ₀ * P

instance (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Decidable (ConjToℓ₀ B) := by
  unfold ConjToℓ₀
  infer_instance

set_option maxRecDepth 10000 in
theorem conjToℓ₀_of_involution : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B * B = 1 → B ≠ 1 →
    ConjToℓ₀ B := by
  decide

@[expose] def mb (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j => B (Fin.castSucc i) (Fin.castSucc j)

theorem apply_two_of_vecMul_v₀ {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : vecMul v₀ B = v₀)
    (j : Fin 3) : B 2 j = v₀ j := by
  rw [← h]
  simp [vecMul, dotProduct, v₀, Fin.sum_univ_three]

theorem mb_mul {B B' : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : vecMul v₀ B' = v₀) :
    mb (B * B') = mb B * mb B' := by
  have h0 := apply_two_of_vecMul_v₀ h 0
  have h1 := apply_two_of_vecMul_v₀ h 1
  ext i j
  fin_cases j <;> simp [mb, mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h0, h1, v₀]

theorem mb_one : mb 1 = 1 := by decide

@[expose] def IsO₂ (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  ∃ c : Fin 3 → ZMod 2, v₀ ⬝ᵥ c = 0 ∧ B = lv c v₀

instance (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Decidable (IsO₂ B) := by
  unfold IsO₂
  infer_instance

set_option maxRecDepth 10000 in
theorem isO₂_of_mb_eq_one : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), vecMul v₀ B = v₀ →
    mb B = 1 → IsO₂ B := by
  decide

@[expose] def HasStabLift (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Prop :=
  ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B.det = 1 ∧ vecMul v₀ B = v₀ ∧ mb B = M

instance (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Decidable (HasStabLift M) := by
  unfold HasStabLift
  infer_instance

set_option maxRecDepth 10000 in
theorem hasStabLift : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 2), M.det ≠ 0 → HasStabLift M := by
  decide

theorem mb_τ₀_ne_one : mb τ₀ ≠ 1 := by decide

theorem mb_τ₀_sq : mb τ₀ * mb τ₀ = 1 := by decide

@[expose] def InU3 (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  B 0 0 = 1 ∧ B 1 0 = 0 ∧ B 2 0 = 0 ∧ B 1 1 = 1 ∧ B 2 1 = 0 ∧ B 2 2 = 1

instance (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Decidable (InU3 B) := by
  unfold InU3
  infer_instance

set_option maxRecDepth 10000 in
theorem inU3_of_commute : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B * ℓ₀ = ℓ₀ * B →
    B.det ≠ 0 → InU3 B := by
  decide

set_option maxRecDepth 10000 in
theorem commute_of_inU3 : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), InU3 B →
    B * ℓ₀ = ℓ₀ * B ∧ B.det = 1 := by
  decide

set_option maxRecDepth 10000 in
theorem commute_or_of_inU3 : ∀ B B' : Matrix (Fin 3) (Fin 3) (ZMod 2), InU3 B → InU3 B' →
    B * B' = B' * B ∨ B * B' = ℓ₀ * (B' * B) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem card_inU3 : Fintype.card {B : Matrix (Fin 3) (Fin 3) (ZMod 2) // InU3 B} = 8 := by
  decide

theorem inU3_lv_e₁ : InU3 (lv ![0, 1, 0] v₀) := by decide

theorem vecMul_ℓ₀_eq_iff : ∀ u : Fin 3 → ZMod 2, vecMul u ℓ₀ = u ↔ u 0 = 0 := by
  decide

theorem top_eq_of_rank_two : ∀ a : Fin 3 → ZMod 2, a + vecMul a ℓ₀ = 0 →
    (∃ w : Fin 3 → ZMod 2, a ⬝ᵥ w = 1 ∧ w + ℓ₀ *ᵥ w = 0) → a = ![0, 1, 0] ∨ a = ![0, 1, 1] := by
  decide

set_option maxRecDepth 10000 in
theorem exists_top_of_inU3 : ∀ a : Fin 3 → ZMod 2, (a = ![0, 1, 0] ∨ a = ![0, 1, 1]) →
    ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), InU3 B →
      ∃ b : Fin 3 → ZMod 2, b + vecMul b ℓ₀ = a + vecMul a B := by
  decide

set_option maxRecDepth 10000 in
theorem exists_of_mulVec_eq : ∀ a : Fin 3 → ZMod 2, (a = ![0, 1, 0] ∨ a = ![0, 1, 1]) →
    ∀ w : Fin 4 → ZMod 2, GL4.mk4 a ℓ₀ *ᵥ w = w →
      ∃ u : Fin 4 → ZMod 2, u + GL4.mk4 a ℓ₀ *ᵥ u = w := by
  decide

set_option maxRecDepth 10000 in
theorem card_fixed_four : ∀ a : Fin 3 → ZMod 2, (a = ![0, 1, 0] ∨ a = ![0, 1, 1]) →
    Fintype.card {w : Fin 4 → ZMod 2 // GL4.mk4 a ℓ₀ *ᵥ w = w} = 4 := by
  decide

end CFSG.CGT.M24S.NSB
