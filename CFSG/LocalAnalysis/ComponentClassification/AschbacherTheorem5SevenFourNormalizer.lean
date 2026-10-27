module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open CFSG.ComponentClassification.AschbacherTightEmbedding

theorem exists_conj_le_normalizer {K : Type} [Group K] {p : ℕ} [Fact p.Prime]
    {S T : Subgroup K} [Finite S]
    (hS : IsPGroup p S) (hTS : T ≤ S) {x : K} (hx : rightConjugate T x ≤ S)
    (hne : rightConjugate T x ≠ T) :
    ∃ y : K, rightConjugate T y ≤ S ⊓ Subgroup.normalizer (T : Set K) ∧
      rightConjugate T y ≠ T := by
  by_contra hcon
  push Not at hcon
  have hTN : T ≤ Subgroup.normalizer (T : Set K) := Subgroup.le_normalizer
  have : Group.IsNilpotent S := hS.isNilpotent
  have hNtop : (Subgroup.normalizer (T : Set K)).subgroupOf S = ⊤ := by
    by_contra hNne
    obtain ⟨g, hgN, hgnot⟩ := IsConcreteLE.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent _ (lt_top_iff_ne_top.mpr hNne))
    apply hgnot
    rw [Subgroup.mem_subgroupOf, ← rightConjugate_eq_self_iff]
    apply hcon
    intro t ht
    rw [mem_rightConjugate_iff] at ht
    have hu : (⟨(g : K) * t * (g : K)⁻¹, hTS ht⟩ : S) ∈
        (Subgroup.normalizer (T : Set K)).subgroupOf S :=
      Subgroup.mem_subgroupOf.mpr (hTN ht)
    have hmem := (Subgroup.mem_normalizer_iff''.mp hgN _).mp hu
    have heq : ((g⁻¹ * ⟨(g : K) * t * (g : K)⁻¹, hTS ht⟩ * g : S) : K) = t := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [Subgroup.mem_subgroupOf, heq] at hmem
    refine Subgroup.mem_inf.mpr ⟨?_, hmem⟩
    rw [← heq]
    exact Subtype.property _
  have hSN : S ≤ Subgroup.normalizer (T : Set K) := by
    intro s hs
    have h : (⟨s, hs⟩ : S) ∈ (Subgroup.normalizer (T : Set K)).subgroupOf S :=
      hNtop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp h
  exact hne (hcon x (le_inf hx (hx.trans hSN)))

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
