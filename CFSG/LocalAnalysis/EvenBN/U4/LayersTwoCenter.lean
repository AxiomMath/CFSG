module

public import CFSG.LocalAnalysis.EvenBN.U4.LayersTwo
import CFSG.LocalAnalysis.EvenBN.Common.SL2FourCenter

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}


theorem sec3_12_two_center_all (hS : Setting h L η t Q T) :
    center (miyamotoM2G h L η t Q) = ⊥ := by
  rcases Nat.lt_or_ge f 3 with hf | hf
  · have hf2 : f = 2 := by have := hS.two_le; omega
    subst hf2
    obtain ⟨-, -, -, hMM, -, hZodd, hXor, -⟩ := hS.sec3_12_two
    have : Group.IsPerfect (miyamotoM2G h L η t Q) := by
      refine ⟨?_⟩
      apply Subgroup.map_injective (miyamotoM2G h L η t Q).subtype_injective
      rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, hMM]
    rcases hXor.or with ⟨k, _, _, hk, ψ, -⟩ | ⟨k₂, _, _, hk₂, ψ, -⟩
    · exact Common.center_eq_bot_of_sl2_four_prod (by rw [Nat.card_eq_fintype_card, hk]; norm_num)
        hZodd ψ
    · refine Common.center_eq_bot_of_sl2 ?_ ?_ ψ <;> rw [Nat.card_eq_fintype_card, hk₂] <;>
        norm_num
  · exact hS.sec3_12_two_center hf

theorem sec3_12_two_iso_all (hS : Setting h L η t Q T) :
    Xor
      (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ f ∧
        ∃ (ψ : miyamotoM2G h L η t Q ≃* SL(2, k) × SL(2, k))
          (α : miyamotoN2G h L η ≃* SL(2, k)),
          (∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
            ψ x = (α a, α a)) ∧
          ∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
            ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
      (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ f) ^ 2 ∧
        ∃ ψ : miyamotoM2G h L η t Q ≃* SL(2, k₂),
          (∀ x y : miyamotoM2G h L η t Q, (y : G) = t⁻¹ * x * t →
            ((ψ y : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
              (ψ x : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ f)) ∧
          ∀ g : SL(2, k₂),
            g ∈ ((miyamotoN2G h L η).subgroupOf (miyamotoM2G h L η t Q)).map ψ.toMonoidHom ↔
              ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ f =
                (g : Matrix (Fin 2) (Fin 2) k₂) i j) := by
  obtain ⟨-, -, -, -, -, -, hXor, -⟩ := hS.sec3_12_two
  have hZ := hS.sec3_12_two_center_all
  set M := miyamotoM2G h L η t Q with hMdef
  let c : M ≃* M ⧸ center M :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hc : ∀ x : M, c x = (x : M ⧸ center M) := fun x =>
    (MulEquiv.symm_apply_eq _).2 rfl
  have hcm : c.toMonoidHom = QuotientGroup.mk' (center M) := MonoidHom.ext hc
  have hexcl : ∀ (k : Type) (_ : Field k) (_ : Fintype k) (k₂ : Type) (_ : Field k₂)
      (_ : Fintype k₂), Fintype.card k₂ = (2 ^ f) ^ 2 →
      (M ⧸ center M ≃* SL(2, k) × SL(2, k)) → (M ≃* SL(2, k₂)) → False := by
    intro k _ _ k₂ _ _ hk₂ ψ₁ ψ₂
    have hk₂' : Nat.card k₂ = 2 ^ (2 * f) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
    exact (GMS.isEmpty_mulEquiv_sl2_prod (k := k) (by have := hS.two_le; omega) hk₂').false
      ((ψ₂.symm.trans c).trans ψ₁)
  rcases hXor with ⟨⟨k, _, _, hk, ψ, α, hψA, hψt⟩, -⟩ | ⟨⟨k₂, _, _, hk₂, ψ, hψt, hψA⟩, -⟩
  · refine Or.inl ⟨⟨k, inferInstance, inferInstance, hk, c.trans ψ, α, fun a x hxa => ?_,
      fun x y y₁ y₂ hxy hx => ?_⟩, ?_⟩
    · rw [MulEquiv.trans_apply, hc]
      exact hψA a x hxa
    · rw [MulEquiv.trans_apply, hc] at hx ⊢
      exact hψt x y y₁ y₂ hxy hx
    · rintro ⟨k₂, _, _, hk₂, ψ₂, -⟩
      exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂ ψ ψ₂
  · refine Or.inr ⟨⟨k₂, inferInstance, inferInstance, hk₂, c.trans ψ, fun x y hxy => ?_,
      fun g => ?_⟩, ?_⟩
    · rw [MulEquiv.trans_apply, hc, MulEquiv.trans_apply, hc]
      exact hψt x y hxy
    · rw [← hψA g, ← hcm, map_map]
      rfl
    · rintro ⟨k, _, _, -, ψ₁, -⟩
      exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂
        (c.symm.trans ψ₁) (c.trans ψ)

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
