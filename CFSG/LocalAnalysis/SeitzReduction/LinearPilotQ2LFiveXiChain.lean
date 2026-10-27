module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveXiC

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup
open scoped commutatorElement

section Chain

variable {H : Type*} [Group H]

@[expose] def seitzChainStep (N : Subgroup H) [N.Normal] : Subgroup H where
  carrier := {x : H | ∀ y ∈ commutator H, ⁅x, y⁆ ∈ N}
  one_mem' := by
    intro y _
    simp
  mul_mem' := by
    intro a b ha hb y hy
    have h1 : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact mul_mem (Subgroup.Normal.conj_mem inferInstance _ (hb y hy) a) (ha y hy)
  inv_mem' := by
    intro a ha y hy
    have h1 : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact Subgroup.Normal.conj_mem inferInstance _ (inv_mem (ha y hy)) a⁻¹

instance seitzChainStep_characteristic (N : Subgroup H) [N.Characteristic] :
    (seitzChainStep N).Characteristic := by
  refine characteristic_iff_le_comap.2 fun φ x hx y hy => ?_
  have hy' : φ.symm y ∈ commutator H :=
    characteristic_iff_le_comap.1 (inferInstance : (commutator H).Characteristic) φ.symm hy
  have h1 : ⁅φ x, y⁆ = φ ⁅x, φ.symm y⁆ := by
    rw [map_commutatorElement, MulEquiv.apply_symm_apply]
  change ⁅φ x, y⁆ ∈ N
  rw [h1]
  exact characteristic_iff_le_comap.1 (inferInstance : N.Characteristic) φ (hx _ hy')

variable (H) in
@[expose] def seitzChainAux : ℕ → Σ' N : Subgroup H, N.Characteristic
  | 0 => ⟨⊥, inferInstance⟩
  | n + 1 =>
    let un := seitzChainAux n
    let _un_characteristic := un.2
    ⟨seitzChainStep un.1, inferInstance⟩

variable (H) in
@[expose] def seitzChain (k : ℕ) : Subgroup H := (seitzChainAux H k).1

instance seitzChain_characteristic (k : ℕ) : (seitzChain H k).Characteristic :=
  (seitzChainAux H k).2

theorem seitzChain_zero : seitzChain H 0 = ⊥ := rfl

theorem mem_seitzChain_succ (k : ℕ) {x : H} :
    x ∈ seitzChain H (k + 1) ↔ ∀ y ∈ commutator H, ⁅x, y⁆ ∈ seitzChain H k := Iff.rfl

end Chain

open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

@[expose] def LFiveGraphSylowChainInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ g ∈ centralizer ({t} : Set G), ∀ l ∈ L, ∃ x ∈ L, g * x * g⁻¹ ≠ l * x * l⁻¹) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ (S₀ : Subgroup G) (d : G), IsLFiveFieldSylow L t (seitzTilde W₁ Kc) S₀ →
      IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d →
      S₀.subgroupOf (S₀ ⊔ zpowers d ⊔ zpowers t) =
        seitzChain (S₀ ⊔ zpowers d ⊔ zpowers t : Subgroup G) 4

theorem lFiveGraphSylowCharInput_of_chain (h : LFiveGraphSylowChainInput) :
    LFiveGraphSylowCharInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ d hS₀
    hdata
  rw [h G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ d hS₀ hdata]
  infer_instance

end CFSG.SeitzReduction.LinearPilot
