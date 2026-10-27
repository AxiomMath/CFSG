module

public import Certificates.Certificate4044

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.A8

open Equiv Equiv.Perm

theorem g5_sign : ∀ a b : Fin 8, a ≠ b → sign (g5 a b) = 1 := by decide

theorem g3_sign : ∀ a b : Fin 8, a ≠ b → sign (g3 a b) = 1 := by decide

theorem g5_fix : ∀ a b : Fin 8, a ≠ b → g5 a b a = a ∧ g5 a b b = b := by decide

theorem g3_fix : ∀ a b : Fin 8, a ≠ b → g3 a b a = a ∧ g3 a b b = b := by decide

theorem card_sdiff_pair :
    ∀ a b : Fin 8, a ≠ b → (Finset.univ \ {a, b} : Finset (Fin 8)).card = 6 := by decide

theorem cent_g :
    ∀ a b : Fin 8, a ≠ b → ∀ τ : Perm (Fin 8), τ * g5 a b = g5 a b * τ →
    τ * g3 a b = g3 a b * τ → τ = 1 ∨ τ = swap a b :=
  Certificates.certificate4044

end CFSG.QuasithinUnique.Id2519.Tab.A8
