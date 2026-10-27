module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.CentralSquares

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (card_sup_mul_card_inf_eq)
open scoped commutatorElement

theorem exists_eq_inv_mul_conj_of_inf_centralizer_eq_bot {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {x : G} (hx : x ∈ normalizer (A : Set G))
    (hC : A ⊓ centralizer ({x} : Set G) = ⊥) {a : G} (ha : a ∈ A) :
    ∃ b ∈ A, a = b⁻¹ * (x * b * x⁻¹) := by
  have hconj : ∀ b ∈ A, x * b * x⁻¹ ∈ A := fun b hb => (mem_normalizer_iff.1 hx b).1 hb
  let φ : A → A := fun b => ⟨(b : G)⁻¹ * (x * b * x⁻¹), mul_mem (inv_mem b.2) (hconj b b.2)⟩
  have hinj : Function.Injective φ := by
    intro b b' hbb
    have e : (b : G)⁻¹ * (x * b * x⁻¹) = (b' : G)⁻¹ * (x * b' * x⁻¹) := congrArg Subtype.val hbb
    set c : G := (b' : G) * (b : G)⁻¹
    have hcA : c ∈ A := mul_mem b'.2 (inv_mem b.2)
    have hxc : x * c * x⁻¹ = c := by
      have hX := hconj b b.2
      have hX' := hconj b' b'.2
      have e1 : (b' : G) * ((b : G)⁻¹ * (x * b * x⁻¹)) = x * b' * x⁻¹ := by
        rw [e, mul_inv_cancel_left]
      have e2 : c * (x * b * x⁻¹) = x * b' * x⁻¹ := by
        rw [← e1, mul_assoc]
      have e3 : x * c * x⁻¹ = (x * b' * x⁻¹) * (x * b * x⁻¹)⁻¹ := by
        simp only [c]
        group
      rw [e3, ← e2, mul_inv_cancel_right]
    have hcC : c ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc c * x = x * c * x⁻¹ * x := by rw [hxc]
        _ = x * c := by group
    have hc1 : c = 1 := by
      have : c ∈ (⊥ : Subgroup G) := hC ▸ mem_inf.2 ⟨hcA, hcC⟩
      exact mem_bot.1 this
    refine Subtype.ext ?_
    have : (b' : G) = b := by
      have := congrArg (· * (b : G)) hc1
      simpa [c] using this
    exact this.symm
  have : Finite A := inferInstance
  obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨a, ha⟩
  exact ⟨b, b.2, (congrArg Subtype.val hb).symm⟩

end CFSG.LocalAnalysis.EvenBN.U4
