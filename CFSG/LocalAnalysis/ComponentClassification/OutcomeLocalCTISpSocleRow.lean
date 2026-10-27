module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem sp_socle_row {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ 2)
    {σ : K ≃+* K} (hσ : ∀ t, σ t = t ^ 2) {γ : MulAut (StatedProj (StatedSp 2 K))}
    (hγ : ∀ g : StatedSp 2 K, γ (proj 2 K g) = proj 2 K (exceptionalSpAut K g))
    (hι₀ : Function.Injective ((spInner 2 K).comp (subfieldSpHom 2 (descentField σ))))
    (hIC : centralizer {fieldAut 2 K σ} ⊓ OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) =
      ((spInner 2 K).comp (subfieldSpHom 2 (descentField σ))).range) :
    orderOf γ = 4 ∧ γ ^ 2 = fieldAut 2 K σ ∧
      centralizer {fieldAut 2 K σ} =
        ((spInner 2 K).comp (subfieldSpHom 2 (descentField σ))).range ⊔ zpowers γ ∧
      ((spInner 2 K).comp (subfieldSpHom 2 (descentField σ))).range ⊓ zpowers γ = ⊥ ∧
      (∀ n ∈ ((spInner 2 K).comp (subfieldSpHom 2 (descentField σ))).range,
        γ * n * γ⁻¹ ∈ ((spInner 2 K).comp (subfieldSpHom 2 (descentField σ))).range) ∧
      (∀ α ∈ centralizer {fieldAut 2 K σ}, ∃! q : StatedSp 2 (descentField σ) × Fin 4,
        α = (spInner 2 K).comp (subfieldSpHom 2 (descentField σ)) q.1 * γ ^ (q.2 : ℕ)) ∧
      (((spInner 2 K).comp (subfieldSpHom 2 (descentField σ))).range.subgroupOf
        (centralizer {fieldAut 2 K σ})).Normal := by
  set ι₀ := (spInner 2 K).comp (subfieldSpHom 2 (descentField σ)) with hι₀def
  set N₀ := ι₀.range with hN₀
  set β := fieldAut 2 K σ with hβ
  obtain ⟨-, -, -, -, -, hall⟩ := even_symplectic_two_exterior_square_automorphism
    (f := 2) (by norm_num) hK
  obtain ⟨hsq, hord, -, huniq, hinf, -⟩ := hall γ hγ
  have hγ2 : γ ^ 2 = β := hsq σ hσ
  have hγC : γ ∈ centralizer {β} := by
    rw [mem_centralizer_singleton_iff, ← hγ2, ← pow_succ, ← pow_succ']
  have hpowC : ∀ j : ℕ, γ ^ j ∈ centralizer {β} := fun j => pow_mem hγC j
  have hNC : N₀ ≤ centralizer {β} := by
    rw [← hIC]
    exact inf_le_left
  have hNI : N₀ ≤ OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) := by
    rw [← hIC]
    exact inf_le_right
  have hinnC : ∀ g : StatedSp 2 K, spInner 2 K g ∈ centralizer {β} → spInner 2 K g ∈ N₀ := by
    intro g hg
    rw [← hIC]
    exact mem_inf.mpr ⟨hg, spInner_mem_inner g⟩
  have hfac : ∀ α ∈ centralizer {β}, ∀ g : StatedSp 2 K, ∀ j : ℕ, α = spInner 2 K g * γ ^ j →
      spInner 2 K g ∈ N₀ := by
    intro α hα g j hgj
    refine hinnC g ?_
    have : spInner 2 K g = α * (γ ^ j)⁻¹ := by rw [hgj, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hα (inv_mem (hpowC j))
  refine ⟨by omega, hγ2, le_antisymm ?_ (sup_le hNC (zpowers_le.mpr hγC)), ?_, ?_, ?_, ?_⟩
  · intro α hα
    obtain ⟨⟨g, j⟩, hgj, -⟩ := huniq α
    have hgj' : α = spInner 2 K g * γ ^ (j : ℕ) := hgj
    rw [hgj']
    exact mul_mem (mem_sup_left (hfac α hα g j hgj'))
      (mem_sup_right (pow_mem (mem_zpowers γ) _))
  · rw [eq_bot_iff, ← hinf]
    exact inf_le_inf_right _ hNI
  · intro n hn
    rw [← hIC] at hn ⊢
    obtain ⟨hnC, hnI⟩ := mem_inf.mp hn
    exact mem_inf.mpr ⟨mul_mem (mul_mem hγC hnC) (inv_mem hγC),
      (OuterAutomorphisms.inner_normal _).conj_mem n hnI γ⟩
  · intro α hα
    obtain ⟨⟨g, j⟩, hgj, hu⟩ := huniq α
    have hgj' : α = spInner 2 K g * γ ^ (j : ℕ) := hgj
    obtain ⟨v, hv⟩ := hfac α hα g j hgj'
    refine ⟨(v, ⟨j, by have := j.2; omega⟩), ?_, ?_⟩
    · change α = ι₀ v * γ ^ (j : ℕ)
      rw [hv, hgj']
    · rintro ⟨v', j'⟩ hv'
      have hv'' : α = spInner 2 K (subfieldSpHom 2 (descentField σ) v') * γ ^ (j' : ℕ) := hv'
      have h1 := hu (subfieldSpHom 2 (descentField σ) v', ⟨j', by have := j'.2; omega⟩) hv''
      have h2 : subfieldSpHom 2 (descentField σ) v' = g := congrArg Prod.fst h1
      have h3 : (j' : ℕ) = j := congrArg (fun q : StatedSp 2 K × Fin (2 * 2) => (q.2 : ℕ)) h1
      have h4 : v' = v := by
        apply hι₀
        change spInner 2 K (subfieldSpHom 2 (descentField σ) v') = ι₀ v
        rw [h2, hv]
      rw [h4]
      exact Prod.ext rfl (Fin.ext h3)
  · refine ⟨fun x hx c => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    rw [← hIC] at hx ⊢
    obtain ⟨hxC, hxI⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨mul_mem (mul_mem c.2 hxC) (inv_mem c.2),
      (OuterAutomorphisms.inner_normal _).conj_mem _ hxI c⟩

end CFSG.ComponentClassification.OutcomeLocal
