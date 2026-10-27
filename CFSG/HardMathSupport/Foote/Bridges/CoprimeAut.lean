module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Foote.Bridges

open SemidirectProduct

abbrev zpowersAction (K : Type) [Group K] (φ : MulAut K) : Subgroup.zpowers φ →* MulAut K :=
  (Subgroup.zpowers φ).subtype

lemma center_eq_bot_of_simple {K : Type} [Group K] (hS : IsSimpleGroup K)
    (hnc : ∃ a b : K, a * b ≠ b * a) : Subgroup.center K = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center K) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnc
    have hb : b ∈ Subgroup.center K := by rw [h]; exact Subgroup.mem_top b
    exact absurd (Subgroup.mem_center_iff.mp hb a) hab

lemma isPerfect_of_simple {K : Type} [Group K] (hS : IsSimpleGroup K)
    (hnc : ∃ a b : K, a * b ≠ b * a) : Group.IsPerfect K := by
  rw [Group.isPerfect_def]
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator K) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hm : a * b * a⁻¹ * b⁻¹ ∈ commutator K :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := by
      rw [h, Subgroup.mem_bot] at hm
      exact hm
    apply hab
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  · exact h

lemma finite_semidirect {N G : Type} [Group N] [Group G] [Finite N] [Finite G]
    (ψ : G →* MulAut N) : Finite (N ⋊[ψ] G) :=
  Finite.of_surjective
    (fun q : N × G => (SemidirectProduct.inl q.1 : N ⋊[ψ] G) * SemidirectProduct.inr q.2)
    (fun x => ⟨(x.left, x.right), SemidirectProduct.inl_left_mul_inr_right x⟩)

lemma fixed_of_comm {N G : Type} [Group N] [Group G] (ψ : G →* MulAut N) (g : G) (t : N)
    (h : (SemidirectProduct.inl t : N ⋊[ψ] G) * SemidirectProduct.inr g =
      SemidirectProduct.inr g * SemidirectProduct.inl t) :
    ψ g t = t := by
  have h2 : (SemidirectProduct.inl (ψ g t) : N ⋊[ψ] G) = SemidirectProduct.inl t := by
    rw [SemidirectProduct.inl_aut, map_inv SemidirectProduct.inr g, ← h, mul_inv_cancel_right]
  exact SemidirectProduct.inl_injective h2

end CFSG.HardMathSupport.Foote.Bridges

end
