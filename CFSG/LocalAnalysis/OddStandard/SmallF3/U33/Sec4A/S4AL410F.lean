module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL410E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL410G

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem lemma4_10_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) (h2 : 2 ∣ S.index) (hG2 : 2 ^ 11 ∣ Nat.card G)
    (hE : ∀ 𝒮 : Sylow 2 G, ∃ E : Subgroup G, E ≤ (𝒮 : Subgroup G) ∧
      (E.subgroupOf (𝒮 : Subgroup G)).Normal ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8)
    (h49 : Lemma4_9Concl t S x₁ x₂ tau) : Lemma4_10Concl t x₁ x₂ tau := by
  obtain ⟨h4, h8, h8'⟩ := ncard_tF_cases h h44
  unfold Lemma4_10Concl
  rcases h49.2 with h1 | h1 | h1 | h1
  · exact Or.inl (by rw [h1]; exact h4)
  · exact Or.inr (by rw [h1]; exact h8)
  · exact Or.inr (by rw [h1]; exact h8')
  · exfalso
    have hF1 : (1 : G) ∈ (fourGrp x₁ x₂ : Set G) := (fourGrp x₁ x₂).one_mem
    have hzF : (x₁ * x₂) ^ 2 ∈ (fourGrp x₁ x₂ : Set G) := Subgroup.subset_closure (by simp)
    have hτ : tau ∈ conjIn (ctxM t tau x₁ x₂) t := by
      rw [h1]; exact Or.inl (Or.inr ⟨1, hF1, mul_one tau⟩)
    have htτ : t * tau ∈ conjIn (ctxM t tau x₁ x₂) t := by
      rw [h1]; exact Or.inr ⟨1, hF1, mul_one (t * tau)⟩
    have htz : t * (x₁ * x₂) ^ 2 ∈ conjIn (ctxM t tau x₁ x₂) t := by
      rw [h1]; exact Or.inl (Or.inl ⟨(x₁ * x₂) ^ 2, hzF, rfl⟩)
    obtain ⟨k₁, -, hk₁⟩ := hτ
    obtain ⟨k₂, -, hk₂⟩ := htτ
    obtain ⟨k₃, -, hk₃⟩ := htz
    obtain ⟨𝒮, h𝒮⟩ := exists_sylow_gt h.toCtx0.isPGroup h2
    obtain ⟨E, hE𝒮, hEn, hEe, hEc⟩ := hE 𝒮
    exact false_of_tM_twelve h h43 h44 h2 hG2 ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ ⟨k₃, hk₃⟩ 𝒮 h𝒮 hE𝒮 hEn hEe hEc

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
