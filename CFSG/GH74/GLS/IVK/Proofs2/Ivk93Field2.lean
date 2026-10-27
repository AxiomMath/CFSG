module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PG
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint CFSG.ComponentClassification
open scoped MatrixGroups

namespace Ivk93Cfg2

variable {J : Type} [Group J] [Finite J] {x : J} {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup J}

theorem q_eq_of_equiv_sl2 (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (e : SL(2, F) ≃* ↥L₁) : Nat.card F = q₁ := by
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  have hO : pPrimeCore 2 ↥L₁ = ⊥ := by
    rw [← CFSG.pPrimeCore_map_iso 2 e, CatFactsSp4.pPrimeCore_SL2 h2 (by omega), Subgroup.map_bot]
  have h1 : Nat.card ↥L₁ = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F]
  have h3 := h.card₁
  rw [hO, Subgroup.card_bot, mul_one] at h3
  exact sl2_card_inj h5 h.five₁ (h1.symm.trans h3)

theorem q_eq_of_equiv_sl2' (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (e : SL(2, F) ≃* ↥L₂) : Nat.card F = q₂ :=
  h.symm.q_eq_of_equiv_sl2 hodd h5 e

end Ivk93Cfg2

end CFSG.GH74.GLS.IVK.Proofs2
