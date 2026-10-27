module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.IndexTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.LUniq
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ActionAgrees
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.OuterInvolutions

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup
open scoped commutatorElement

theorem aschbacherUniq :
    ∀ (C C' : Type) [Group C] [Group C'] [Finite C] [Finite C'] (Q : Subgroup C) (Q' : Subgroup C')
      [Q.Normal] [Q'.Normal], AschbacherHyp C Q → AschbacherHyp C' Q' → Nonempty (C ≃* C') := by
  intro C C' _ _ _ _ Q Q' _ _ hC hC'
  obtain ⟨t, ht⟩ := hC.exists_isOuterInvolution
  obtain ⟨t', ht'⟩ := hC'.exists_isOuterInvolution
  obtain ⟨α⟩ := hC.nonempty_mulEquiv_commutator hC'
  obtain ⟨τ, hτL, hτ⟩ := hC.exists_conj_of_isOuterInvolution hC' α ht
  have htt : t * t = 1 := by rw [← pow_two]; exact ht.2.1
  have hτ2 : τ ^ 2 ∈ centerOf Q' := by
    refine hC'.centralizer_commutator_le ?_
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨l, hl⟩ := α.surjective ⟨y, hy⟩
    have h1 := hτ l
    have h2 := hτ (MulAut.conjNormal t l)
    have h3 : MulAut.conjNormal t (MulAut.conjNormal t l) = l := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply]
      calc t * (t * (l : C) * t⁻¹) * t⁻¹ = (t * t) * (l : C) * (t * t)⁻¹ := by group
        _ = l := by rw [htt]; group
    rw [h3, h1] at h2
    have hy' : y = (α l : C') := by rw [hl]
    rw [hy']
    calc (α l : C') * τ ^ 2 = (τ * (τ * (α l : C') * τ⁻¹) * τ⁻¹) * τ ^ 2 := by rw [← h2]
      _ = τ ^ 2 * (α l : C') := by rw [pow_two]; group
  obtain ⟨g, z, hz, hg⟩ := hC'.exists_conj_of_sq_mem_centerOf hτL ht'.1 hτ2
    (by rw [ht'.2.1]; exact one_mem _)
  have hzc : z ∈ Subgroup.center C' := hC'.centerOf_le_center hz
  have hz' := Subgroup.mem_center_iff.mp hzc
  set t₂ : C' := g⁻¹ * t' * g with ht₂def
  have hτt₂ : τ = t₂ * z := by
    calc τ = g⁻¹ * (g * τ * g⁻¹) * g := by group
      _ = g⁻¹ * (t' * z) * g := by rw [hg]
      _ = g⁻¹ * t' * (z * g) := by group
      _ = g⁻¹ * t' * (g * z) := by rw [← hz' g]
      _ = t₂ * z := by rw [ht₂def]; group
  have ht₂L : t₂ ∉ commutator C' := by
    intro h
    apply ht'.1
    have h' : g * t₂ * g⁻¹ ∈ commutator C' :=
      (inferInstance : (commutator C').Normal).conj_mem t₂ h g
    have e : g * t₂ * g⁻¹ = t' := by rw [ht₂def]; group
    rwa [e] at h'
  have ht₂2 : t₂ ^ 2 = 1 := by
    have : t₂ ^ 2 = g⁻¹ * t' ^ 2 * g := by rw [ht₂def, pow_two, pow_two]; group
    rw [this, ht'.2.1]
    group
  have hconj : ∀ l : ↥(commutator C),
      ((α (MulAut.conjNormal t l) : ↥(commutator C')) : C') = t₂ * (α l : C') * t₂⁻¹ := by
    intro l
    rw [hτ l, hτt₂]
    calc t₂ * z * (α l : C') * (t₂ * z)⁻¹ = t₂ * (z * (α l : C') * z⁻¹) * t₂⁻¹ := by group
      _ = t₂ * (α l : C') * t₂⁻¹ := by rw [← hz' (α l : C')]; group
  exact exists_mulEquiv_of_outer_involutions hC.index_commutator hC'.index_commutator α ht.1 ht₂L
    ht.2.1 ht₂2 hconj

end CFSG.EvenSporadicStandard.HNRecog
