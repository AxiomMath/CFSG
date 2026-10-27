module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoTen

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  mem_normalizer_sup card_sup_mul_card_inf_eq)
open scoped MatrixGroups Pointwise commutatorElement

section Generic

theorem prodFactorTwo_trans_prodComm {G S : Type*} [Group G] [Group S] {M : Subgroup G}
    (ψ : M ≃* S × S) : prodFactorTwo (ψ.trans (MulEquiv.prodComm)) = prodFactorOne ψ := by
  ext x
  rw [Common.mem_prodFactorTwo_iff, Common.mem_prodFactorOne_iff]
  simp only [MulEquiv.trans_apply, MulEquiv.coe_prodComm, Prod.fst_swap]

end Generic

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

local notation "𝓥" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

local notation "𝓨" => CFSG.centerIn 𝓤 ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (miyamotoR1G h L η))) (CFSG.centerIn 𝓤)

local notation "𝓨t" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨

local notation "𝓚" => 𝓨t ⊔ prodFactorOne ψ

local notation "𝓦'" => miyamotoRG h L η t Q ⊓ 𝓚

local notation "𝓦'ᵗ" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦'

local notation "𝓦₂" => 𝓦' ⊓ miyamotoF2G h L η t Q

local notation "𝓔₂" => miyamotoEG h L η Q ⊓ 𝓦'ᵗ


theorem exists_case_two_j [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    (ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)) (α₂ : miyamotoN2G h L η ≃* SL(2, k₂))
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a))
    (hψt₂ : ∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k₂)), (y : G) = t⁻¹ * x * t →
      ψ₂ x = (y₁, y₂) → ψ₂ y = (y₂, y₁)) :
    ∃ ψ₂' : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂),
      (∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
        ψ₂' x = (α₂ a, α₂ a)) ∧
      (∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k₂)), (y : G) = t⁻¹ * x * t →
        ψ₂' x = (y₁, y₂) → ψ₂' y = (y₂, y₁)) ∧
      ∃ j ∈ miyamotoJ2G h L η t Q, j ≠ 1 ∧ j ∈ centralizer ((𝓚 : Subgroup G) : Set G) ∧
        j ∈ prodFactorTwo ψ₂' := by
  obtain ⟨hcard, hJV, -⟩ := hS.J2_two hk₂ hψα₂
  obtain ⟨j, hj, hj1, hjX⟩ := hS.exists_J2_centralizer_X1 hk hψA hJV hcard
  have hjC := hS.mem_centralizer_K1'_of_mem_J2 hk hψA hψt hZ hJV hj hjX
  rcases hS.mem_prodFactor_of_mem_J2 hk hψA hψt hZ hk₂ hψα₂ hψt₂ hj hjC with hjY | hjY
  · refine ⟨ψ₂.trans (MulEquiv.prodComm), ?_, ?_, j, hj, hj1, hjC, ?_⟩
    · intro a x hx
      rw [MulEquiv.trans_apply, hψα₂ a x hx, MulEquiv.coe_prodComm, Prod.swap_prod_mk]
    · intro x y y₁ y₂ hy hx
      rw [MulEquiv.trans_apply, MulEquiv.coe_prodComm] at hx ⊢
      have hx' : ψ₂ x = (y₂, y₁) := by
        rw [← Prod.swap_swap (ψ₂ x), hx, Prod.swap_prod_mk]
      rw [hψt₂ x y y₂ y₁ hy hx', Prod.swap_prod_mk]
    · rw [prodFactorTwo_trans_prodComm]
      exact hjY
  · exact ⟨ψ₂, hψα₂, hψt₂, j, hj, hj1, hjC, hjY⟩

theorem exists_D [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    (ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)) (α₂ : miyamotoN2G h L η ≃* SL(2, k₂))
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a))
    (hψt₂ : ∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k₂)), (y : G) = t⁻¹ * x * t →
      ψ₂ x = (y₁, y₂) → ψ₂ y = (y₂, y₁)) :
    ∃ D : Subgroup G, 𝓦' ≤ D ∧ miyamotoR2G h L η ∈ normalizer (D : Set G) ∧
      ∃ hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥,
        D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥ ∧
        (Common.diagonalHom D t hcomm).range ≤ miyamotoA2G h L η ⊔ miyamotoN2G h L η := by
  obtain ⟨ψ₂', hψα₂', hψt₂', j, hj, hj1, hjC, hjY⟩ :=
    hS.exists_case_two_j hk hψA hψt hZ hk₂ ψ₂ α₂ hψα₂ hψt₂
  have hcomm := hS.commutator_D_eq_bot hk hψA hψt hZ hk₂ hψt₂' hj hj1 hjC hjY
  exact ⟨_, hS.W'_le_D hk hψA hψt hZ hk₂ hψα₂' hj hj1 hjC hjY,
    hS.R2G_mem_normalizer_D hk hψA hψt hZ hk₂ hj hj1 hjC hjY, hcomm,
    hS.D_inf_eq_bot hk hψA hψt hZ hk₂ hψα₂' hψt₂' hj hj1 hjC hjY,
    (hS.range_diagonalHom_W2_sup_Y1 hk hψA hψt hZ hk₂ hψα₂' hψt₂' hj hj1 hjC hjY hcomm).le⟩

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
