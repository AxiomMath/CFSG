module

public import CFSG.GH74.GLS.IVK.Statements.Sec11

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK

@[expose] def IVK_11_1c_fixed : Prop :=
  ∀ (p n : ℕ), p.Prime → p ≠ 2 → ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H) [K.Normal],
    (HasSL2Model ↥K (fun r => r = p ^ n) ∨ IsL2 ↥K (fun r => r = p ^ n)) →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
        (ρ : Representation (ZMod p) H V), Function.Injective ρ →
          IsSimpleModule (MonoidAlgebra (ZMod p) H) ρ.asModule →
          2 * n < Module.finrank (ZMod p) V → Module.finrank (ZMod p) V < 4 * n →
            (HasSL2Model ↥K (fun r => r = p ^ n) ∧ 3 * Module.finrank (ZMod p) V = 8 * n ∧
              IsSimpleModule (MonoidAlgebra (ZMod p) ↥K) (resRep ρ K).asModule ∧
              ∀ (V' : Type) [AddCommGroup V'] [Module (ZMod p) V'] [Module.Finite (ZMod p) V']
                (ρ' : Representation (ZMod p) H V'), Function.Injective ρ' →
                  Module.finrank (ZMod p) V' = Module.finrank (ZMod p) V →
                  IsSimpleModule (MonoidAlgebra (ZMod p) ↥K) (resRep ρ' K).asModule →
                    Nonempty ((resRep ρ K).asModule ≃ₗ[MonoidAlgebra (ZMod p) ↥K]
                      (resRep ρ' K).asModule)) ∨
            (IsL2 ↥K (fun r => r = p ^ n) ∧ Module.finrank (ZMod p) V = 3 * n ∧
              IsSimpleModule (MonoidAlgebra (ZMod p) ↥K) (resRep ρ K).asModule ∧
              (∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ^ n ∧
                Nonempty (Module.End (MonoidAlgebra (ZMod p) ↥K) (resRep ρ K).asModule ≃+*
                  F₀)) ∧
              ∀ (V' : Type) [AddCommGroup V'] [Module (ZMod p) V'] [Module.Finite (ZMod p) V']
                (ρ' : Representation (ZMod p) H V'), Function.Injective ρ' →
                  Module.finrank (ZMod p) V' = Module.finrank (ZMod p) V →
                  IsSimpleModule (MonoidAlgebra (ZMod p) ↥K) (resRep ρ' K).asModule →
                    Nonempty ((resRep ρ K).asModule ≃ₗ[MonoidAlgebra (ZMod p) ↥K]
                      (resRep ρ' K).asModule))

@[expose] def IVK_11_1b_nat : Prop :=
  ∀ (p n : ℕ), p.Prime → p ≠ 2 → ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H) [K.Normal],
    HasSL2Model ↥K (fun r => r = p ^ n) →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
        (ρ : Representation (ZMod p) H V), Function.Injective ρ →
          Module.finrank (ZMod p) V = 2 * n →
            IsSimpleModule (MonoidAlgebra (ZMod p) ↥K) (resRep ρ K).asModule ∧
              (∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ^ n ∧
                Nonempty (Module.End (MonoidAlgebra (ZMod p) ↥K) (resRep ρ K).asModule ≃+*
                  F₀)) ∧
              ∀ (V' : Type) [AddCommGroup V'] [Module (ZMod p) V'] [Module.Finite (ZMod p) V']
                (ρ' : Representation (ZMod p) H V'), Function.Injective ρ' →
                  Module.finrank (ZMod p) V' = 2 * n →
                    Nonempty ((resRep ρ K).asModule ≃ₗ[MonoidAlgebra (ZMod p) ↥K]
                      (resRep ρ' K).asModule)

end CFSG.GH74.GLS.IVK.Proofs2
