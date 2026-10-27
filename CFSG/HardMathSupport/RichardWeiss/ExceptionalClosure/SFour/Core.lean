module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Support
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasicAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_mem_commutator' {H₁ H₂ : Subgroup G} {x : G}
    (h₁ : x ∈ Subgroup.normalizer (H₁ : Set G)) (h₂ : x ∈ Subgroup.normalizer (H₂ : Set G))
    {v : G} (hv : v ∈ ⁅H₁, H₂⁆) : x * v * x⁻¹ ∈ ⁅H₁, H₂⁆ := by
  rw [Subgroup.commutator_def] at hv ⊢
  induction hv using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    apply Subgroup.subset_closure
    refine ⟨x * a * x⁻¹, (Subgroup.mem_normalizer_iff.1 h₁ a).1 ha, x * b * x⁻¹,
      (Subgroup.mem_normalizer_iff.1 h₂ b).1 hb, ?_⟩
    simp only [commutatorElement_def]; group
  | one => simp
  | mul y z _ _ hy hz =>
    have : x * (y * z) * x⁻¹ = (x * y * x⁻¹) * (x * z * x⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
    have : x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ hy

theorem perm_commute_of_fix {α β : Type*} (c f : Perm (α ⊕ β))
    (hc : ∀ j, c (Sum.inr j) = Sum.inr j) (hf : ∀ p, f (Sum.inl p) = Sum.inl p) :
    c * f = f * c := by
  have hcl : ∀ p, ∃ q, c (Sum.inl p) = Sum.inl q := by
    intro p
    rcases h : c (Sum.inl p) with q | j
    · exact ⟨q, rfl⟩
    · exfalso
      have : c (Sum.inl p) = c (Sum.inr j) := by rw [h, hc]
      exact Sum.inl_ne_inr (c.injective this)
  have hfr : ∀ j, ∃ k, f (Sum.inr j) = Sum.inr k := by
    intro j
    rcases h : f (Sum.inr j) with p | k
    · exfalso
      have : f (Sum.inr j) = f (Sum.inl p) := by rw [h, hf]
      exact Sum.inr_ne_inl (f.injective this)
    · exact ⟨k, rfl⟩
  ext x
  rcases x with p | j
  · obtain ⟨q, hq⟩ := hcl p
    simp only [Perm.mul_apply, hf, hq]
  · obtain ⟨k, hk⟩ := hfr j
    simp only [Perm.mul_apply, hc, hk]

variable [Finite G]

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
