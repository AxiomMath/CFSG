module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.GUKit
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.GUTorus

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.LinearGroups

variable {f : ℕ} {K : Type*} [Field K] [Finite K] (hK : UnitaryFieldData 2 f K)
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  (H : UnitaryPrimaryData hK.bar B x)

omit [Finite K] in
include H in
theorem eq_zero_of_mem_line_component {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hself : dualPoly hK.bar a = a)
    (hline : Module.finrank K (primaryComponent (x : Module.End K V) a) = 1)
    {W : Submodule K V} (hWt : ∀ v ∈ W, ∀ w ∈ W, B v w = 0) {w : V} (hw : w ∈ W)
    (hwa : w ∈ primaryComponent (x : Module.End K V) a) : w = 0 := by
  by_contra hw0
  have hle : primaryComponent (x : Module.End K V) a ≤ W := by
    intro v hv
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hwa⟩ :
      primaryComponent (x : Module.End K V) a) (fun h0 => hw0 (congrArg Subtype.val h0))).mp
        hline ⟨v, hv⟩
    have : c • w = v := congrArg Subtype.val hc
    rw [← this]
    exact W.smul_mem c hw
  have hsep := separatingLeft_primaryComponent_selfDual H ha hself
  have hzero : (⟨w, hwa⟩ : primaryComponent (x : Module.End K V) a) = 0 :=
    hsep ⟨w, hwa⟩ fun u => hWt w hw u (hle u.2)
  exact hw0 (congrArg Subtype.val hzero)

include H in
open scoped Classical in
theorem eq_bot_of_stable_isotropic
    (hself : ∀ a ∈ primaryFactors (x : Module.End K V), dualPoly hK.bar a = a)
    (hdeg : ∑ a ∈ primaryFactors (x : Module.End K V), a.natDegree ≤ 3)
    (hn : 4 ≤ Module.finrank K V) {ν : K} (hν : hK.bar ν * ν = 1) (hν2 : ν ≠ ν⁻¹)
    {W : Submodule K V} (hWt : ∀ v ∈ W, ∀ w ∈ W, B v w = 0)
    (hC : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ sesqSpecialUnitaryGroup B →
      Commute (g : Module.End K V) (x : Module.End K V) → ∀ w ∈ W, (g : Module.End K V) w ∈ W) :
    W = ⊥ := by
  have hsq := H.squarefree
  set F := primaryFactors (x : Module.End K V) with hF
  have hirr : ∀ a ∈ F, Fact (Irreducible a) := fun a ha =>
    ⟨irreducible_of_mem_primaryFactors ha⟩
  have hdegpos : ∀ a ∈ F, 1 ≤ a.natDegree := fun a ha =>
    (hirr a ha).out.natDegree_pos
  have hm1 : ∀ a ∈ F, 1 ≤ primaryMultiplicity (x : Module.End K V) a := by
    intro a ha
    have := hirr a ha
    have : Nontrivial (primaryComponent (x : Module.End K V) a) :=
      Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq ha)
    exact Module.finrank_pos
  set F₂ := F.filter (fun a => 2 ≤ primaryMultiplicity (x : Module.End K V) a) with hF₂
  set F₁ := F.filter (fun a => ¬ 2 ≤ primaryMultiplicity (x : Module.End K V) a) with hF₁
  have hproj : ∀ a ∈ F₂, ∀ w ∈ W, primaryProjection (x : Module.End K V) a w = 0 := by
    intro a ha w hw
    obtain ⟨haF, ha2⟩ := Finset.mem_filter.mp ha
    have := hirr a haF
    exact primaryProjection_eq_zero_of_two_le hK H haF (hself a haF) hWt hC ha2 hw
  have hsum : Module.finrank K V = ∑ a ∈ F, a.natDegree * primaryMultiplicity
      (x : Module.End K V) a := by
    rw [finrank_eq_sum_degree_mul_multiplicity hsq]
    exact Finset.sum_coe_sort F (fun a => a.natDegree * primaryMultiplicity (x : Module.End K V) a)
  have hF₂ne : F₂.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h1 : ∀ a ∈ F, primaryMultiplicity (x : Module.End K V) a = 1 := by
      intro a ha
      by_contra h
      have : a ∈ F₂ := Finset.mem_filter.mpr ⟨ha, by have := hm1 a ha; omega⟩
      rw [hne] at this
      exact absurd this (Finset.notMem_empty a)
    have : Module.finrank K V = ∑ a ∈ F, a.natDegree :=
      hsum.trans (Finset.sum_congr rfl fun a ha => by rw [h1 a ha, mul_one])
    omega
  obtain ⟨c, hc⟩ := hF₂ne
  have hcF := (Finset.mem_filter.mp hc).1
  have hsplit : ∑ a ∈ F₁, a.natDegree + ∑ a ∈ F₂, a.natDegree = ∑ a ∈ F, a.natDegree := by
    rw [add_comm, hF₁, hF₂]
    exact Finset.sum_filter_add_sum_filter_not F _ _
  have hF₂ge : 1 ≤ ∑ a ∈ F₂, a.natDegree :=
    (hdegpos c hcF).trans (Finset.single_le_sum (f := fun a : K[X] => a.natDegree)
      (fun _ _ => Nat.zero_le _) hc)
  have hF₁le : ∑ a ∈ F₁, a.natDegree ≤ 2 := by omega
  have hdeg1 : ∀ a ∈ F₁, a.natDegree = 1 := by
    intro a ha
    obtain ⟨haF, -⟩ := Finset.mem_filter.mp ha
    have := hirr a haF
    have hodd := odd_natDegree_of_selfDual hK
      (coeff_zero_ne_zero_of_mem_primaryFactors hsq haF) (hself a haF)
    have hle : a.natDegree ≤ 2 := (Finset.single_le_sum (f := fun a : K[X] => a.natDegree)
      (fun _ _ => Nat.zero_le _) ha).trans hF₁le
    obtain ⟨k, hk⟩ := hodd
    omega
  have hcard : F₁.card ≤ 2 := by
    calc F₁.card = ∑ a ∈ F₁, 1 := Finset.card_eq_sum_ones _
      _ = ∑ a ∈ F₁, a.natDegree := Finset.sum_congr rfl fun a ha => (hdeg1 a ha).symm
      _ ≤ 2 := hF₁le
  have hline : ∀ a ∈ F₁, Module.finrank K (primaryComponent (x : Module.End K V) a) = 1 := by
    intro a ha
    obtain ⟨haF, ha2⟩ := Finset.mem_filter.mp ha
    have := hirr a haF
    rw [finrank_primaryComponent, hdeg1 a ha]
    have := hm1 a haF
    have h' : primaryMultiplicity (x : Module.End K V) a = 1 := by omega
    rw [one_mul]
    exact h'
  have hdecomp : ∀ w ∈ W, w = ∑ a ∈ F₁, primaryProjection (x : Module.End K V) a w := by
    intro w hw
    have h1 := eq_sum_primaryProjection hsq w
    have h2 := Finset.sum_filter_add_sum_filter_not F
      (fun a => 2 ≤ primaryMultiplicity (x : Module.End K V) a)
      (fun a => primaryProjection (x : Module.End K V) a w)
    rw [Finset.sum_eq_zero (fun a ha => hproj a ha w hw), zero_add] at h2
    exact h1.trans h2.symm
  have hπW : ∀ w ∈ W, ∀ a ∈ F₁, primaryProjection (x : Module.End K V) a w ∈ W := by
    intro w hw a ha
    have haF := (Finset.mem_filter.mp ha).1
    by_cases hb : ∃ b ∈ F₁, b ≠ a
    · obtain ⟨b, hbF₁, hba⟩ := hb
      have hbF := (Finset.mem_filter.mp hbF₁).1
      have hsub : F₁ ⊆ {a, b} := by
        intro y hy
        by_contra hy'
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy'
        have h3 : ({a, b, y} : Finset K[X]) ⊆ F₁ := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact ha
          · exact hbF₁
          · exact hy
        have := Finset.card_le_card h3
        rw [Finset.card_eq_three.mpr ⟨a, b, y, Ne.symm hba, Ne.symm hy'.1, Ne.symm hy'.2, rfl⟩]
          at this
        omega
      have hF₁eq : F₁ = {a, b} := by
        refine Finset.Subset.antisymm hsub ?_
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact ha
        · exact hbF₁
      have hw2 : w = primaryProjection (x : Module.End K V) a w +
          primaryProjection (x : Module.End K V) b w := by
        have := hdecomp w hw
        rwa [hF₁eq, Finset.sum_pair (Ne.symm hba)] at this
      obtain ⟨g, hgSU, hgc, hga, hgb⟩ := exists_special_unitary_block_scalar H haF hbF
        (hself a haF) (hself b hbF) (Ne.symm hba) (hline a ha) (hline b hbF₁) hν
      have hgw := hC g hgSU hgc w hw
      have hgw2 : (g : Module.End K V) w = ν • primaryProjection (x : Module.End K V) a w +
          ν⁻¹ • primaryProjection (x : Module.End K V) b w := by
        conv_lhs => rw [hw2]
        rw [map_add, hga _ (primaryProjection_mem hsq haF w),
          hgb _ (primaryProjection_mem hsq hbF w)]
      have hν0 : ν - ν⁻¹ ≠ 0 := sub_ne_zero.mpr hν2
      have h1 : (ν - ν⁻¹) • primaryProjection (x : Module.End K V) a w =
          (g : Module.End K V) w - ν⁻¹ • w := by
        have hw2' : ν⁻¹ • w = ν⁻¹ • primaryProjection (x : Module.End K V) a w +
            ν⁻¹ • primaryProjection (x : Module.End K V) b w := by
          rw [← smul_add, ← hw2]
        rw [hgw2, hw2']
        module
      have h2 : (g : Module.End K V) w - ν⁻¹ • w ∈ W := W.sub_mem hgw (W.smul_mem _ hw)
      rw [← h1] at h2
      have := W.smul_mem (ν - ν⁻¹)⁻¹ h2
      rwa [smul_smul, inv_mul_cancel₀ hν0, one_smul] at this
    · push Not at hb
      have hF₁eq : F₁ = {a} := by
        ext y
        simp only [Finset.mem_singleton]
        exact ⟨fun hy => hb y hy, fun hy => hy ▸ ha⟩
      have := hdecomp w hw
      rw [hF₁eq, Finset.sum_singleton] at this
      rw [← this]
      exact hw
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  rw [hdecomp w hw]
  refine Finset.sum_eq_zero fun a ha => ?_
  have haF := (Finset.mem_filter.mp ha).1
  exact eq_zero_of_mem_line_component hK H haF (hself a haF) (hline a ha) hWt (hπW w hw a ha)
    (primaryProjection_mem hsq haF w)

end CFSG.HardMathSupport.Curtis.UnitaryLevi
