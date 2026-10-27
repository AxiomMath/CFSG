module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cE16

public section

namespace CFSG.ComponentClassification.HSFLit.KD8c

open Sec8

theorem center_MC : ∀ a : MC, (∀ g ∈ MC.gens, a * g = g * a) → a = 1 ∨ a = MC.k := by
  decide +kernel

theorem zz_MC : ∀ a : MC, a * a = 1 →
    (∀ g ∈ MC.gens, a * g * a⁻¹ * g⁻¹ = 1 ∨ a * g * a⁻¹ * g⁻¹ = MC.k) → inZ a = true := by
  decide +kernel

theorem comm_Zl : ∀ z ∈ Zl, ∀ a : MC, z * a * z⁻¹ * a⁻¹ = 1 ∨ z * a * z⁻¹ * a⁻¹ = MC.k := by
  decide +kernel

theorem k_comm : ∀ a : MC, MC.k * a = a * MC.k := by decide +kernel

theorem phiR_Zl : ∀ j : Fin 8, ∀ z ∈ Zl, phiR j z = z := by decide +kernel

theorem inZ_y : inZ MC.y = false := by decide +kernel

theorem comm_R1 {a b : MC} (ha : inR1 a = true) (hb : inR1 b = true) :
    inZ (a * b * a⁻¹ * b⁻¹) = true := by
  have hai := inR1_inv' a ha
  have hbi := inR1_inv' b hb
  have hab := inR1_mul _ _ ha hb
  have habi := inR1_mul _ _ hab hai
  rw [inZ_iff', inR1_mul _ _ habi hbi, cidx_mul habi hbi, cidx_mul hab hai, cidx_mul ha hb,
    cidx_inv ha, cidx_inv hb]
  simp [Nat.xor_assoc, Nat.xor_comm (cidx b), Nat.xor_self]

@[expose] def fc (j : Fin 8) : Fin 3 → MC → MC
  | 0 => fun r => r * MC.w₂ * r⁻¹ * MC.w₂⁻¹
  | 1 => fun r => r * phiR j r⁻¹
  | _ => fun r => r * (MC.w₂ * phiR j r⁻¹ * MC.w₂⁻¹)

theorem card_M : ∀ j : Fin 8, j ≠ 3 → j ≠ 4 → ∀ c : Fin 3,
    (Finset.univ.filter fun r : MC => inR1 r = true ∧ inZ (fc j c r) = true).card ≤ 32 := by
  decide +kernel

theorem sep_M : ∀ j : Fin 8, j ≠ 3 → j ≠ 4 → ∀ c c' : Fin 3, c ≠ c' →
    ∃ r : MC, inR1 r = true ∧ inZ (fc j c r) = true ∧ inZ (fc j c' r) = false := by
  decide +kernel

end CFSG.ComponentClassification.HSFLit.KD8c
