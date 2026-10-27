module

public import CFSG.GH74.GLS.C3.Prop121.Card7Defs

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3

@[expose] def tau1A : A11 :=
  ⟨swap 8 9 * swap 9 10, mem_alternatingGroup.2 (by decide)⟩

theorem tau1A_comm : tau1A * altY11 = altY11 * tau1A := by
  apply Subtype.ext
  show (swap (8 : Fin 11) 9 * swap 9 10) * Layer3.yPerm (by norm_num : 8 ≤ 11) =
    Layer3.yPerm (by norm_num : 8 ≤ 11) * (swap 8 9 * swap 9 10)
  simp only [Layer3.yPerm, Layer3.xPerm, Layer3.pt]
  decide

@[expose] def tau1 : H11 := ⟨tau1A, mem_centralizer_singleton_iff.2 tau1A_comm⟩

@[expose] def ystar : H11 := ⟨altY11, mem_centralizer_singleton_iff.2 rfl⟩

structure FFacts : Prop where
  ord3 : ∀ f : F7, f ^ 3 = 1 → f ≠ 1 → Ty3 f ∨ Ty33 f
  conj3 : ∀ f : F7, Ty3 f → ∃ k : F7, k * f * k⁻¹ = f0
  card_f0 : ccard F7 f0 f0 = 288
  card_ty33 : ∀ f : F7, Ty33 f → ccard F7 f f = 72
  inv_nm : ∀ f : F7, IsInv f → nm7 (f : Amb 7) = 4 ∨ nm7 (f : Amb 7) = 8
  rz : Nat.card {p : F7 × F7 // p.1 * f0 = f0 * p.1 ∧ p.2 * f0 = f0 * p.2 ∧ XF p.1 ∧ YF p.2 ∧
      x0F ∈ zpowers (p.1 * p.2)} = 27
  N96 : Nat.card {b : F7 // b * f0 = f0 * b ∧ YF b ∧ ccard F7 f0 b = 96} = 3
  N48 : Nat.card {b : F7 // b * f0 = f0 * b ∧ YF b ∧ ccard F7 f0 b = 48} = 6
  Yvals : ∀ b : F7, b * f0 = f0 * b → YF b → ccard F7 f0 b = 96 ∨ ccard F7 f0 b = 48
  c33 : ∀ f : F7, Ty33 f → ∀ b : F7, b * f = f * b → YF b → ccard F7 f b = 12
  nm4_forced : ∀ f : F7, IsInv f → nm7 (f : Amb 7) = 4 →
    (f : Amb 7).2 = 1 ∨ ¬ (Nat.card (centralizer ({f} : Set F7)) ∣ 1152)
  conj_inv40 : ∀ f f' : F7, IsInv f → IsInv f' → (f : Amb 7).2 = 1 → (f' : Amb 7).2 = 1 →
    ∃ k : F7, k * f * k⁻¹ = f'
  sylow_count : ∀ P : Subgroup F7, Nat.card P = 64 → Nat.card {f : P // XF (f : F7)} = 14

structure HFacts : Prop where
  card_H : Nat.card H11 = 1152
  ord3 : ∀ τ : H11, τ ^ 3 = 1 → τ ≠ 1 →
    ((τ = tau1 ∨ τ = tau1⁻¹) ∧ ccard H11 τ τ = 576) ∨ ccard H11 τ τ ≤ 36
  inv_tau1 : ∃ b : H11, b * tau1 * b⁻¹ = tau1⁻¹
  center : ∀ c : H11, (∀ h : H11, h * c = c * h) → c = 1 ∨ c = ystar
  card_B0 : ccard H11 tau1 tau1 = 576
  B0inv : ∀ b : H11, b * tau1 = tau1 * b → IsInv b → b ≠ ystar →
    ccard H11 tau1 b = 48 ∨ ccard H11 tau1 b = 96
  ry : ∀ X' : Set H11,
    (∀ a ∈ X', a * tau1 = tau1 * a ∧ IsInv a) → ystar ∉ X' →
    (∀ a ∈ X', ∀ g : H11, g * tau1 = tau1 * g → g * a * g⁻¹ ∈ X') →
    Nat.card {b : H11 // b ∈ X' ∧ ccard H11 tau1 b = 96} = 6 →
    Nat.card {b : H11 // b ∈ X' ∧ ccard H11 tau1 b = 48} = 12 →
    Nat.card X' = 18 →
    Nat.card {p : H11 × H11 // p.1 ∈ X' ∧ (p.2 * tau1 = tau1 * p.2 ∧ IsInv p.2 ∧ p.2 ∉ X') ∧
      ystar ∈ zpowers (p.1 * p.2)} = 156

end CFSG.GH74.GLS.C3.Prop121.Card7
