module

public import CFSG.ClassicalInvolution.AschTight.Basic

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem mem_omegaNbr_of_commuting_sylow (ht : S19R.TightStdDelta p f K z) {g : G}
    (hg : g ∉ Subgroup.normalizer (K : Set G)) {P₁ P₂ : Subgroup G} (hP₁ : IsSylow2Of P₁ K)
    (hP₂ : IsSylow2Of P₂ (conjSubgroup g K)) (hcomm : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x) :
    conjSubgroup g K ∈ Asc77.omegaNbr (CoreAssembly.conjClass K) K := by
  have hzP₁ := mem_of_isSylow2Of_of_tight ht hP₁
  obtain ⟨T, hT⟩ := hP₂.exists_sylow
  refine ⟨⟨g, rfl⟩, fun h => hg (conjSubgroup_eq_self_iff.mp h), P₂,
    ⟨conjSubgroup g K, ⟨g, rfl⟩, T, hT.symm⟩, hP₂.1, ?_⟩
  intro y hy
  rw [normalizer_eq_centralizer_of_tight ht, Subgroup.mem_centralizer_singleton_iff]
  exact (hcomm z hzP₁ y hy).symm

theorem commutingSylowForcesCommuting_of_tightD (ht : S19R.TightStd p f K z) :
    CommutingSylowForcesCommuting K := by
  intro g hg P₁ P₂ hP₁ hP₂ hcomm
  exact absurd (Or.inl (mem_omegaNbr_of_commuting_sylow ht.toTightBranch hg hP₁ hP₂ hcomm))
    (ht.edgeless K (CoreAssembly.mem_conjClass_self K) _ ⟨g, rfl⟩)

theorem tightCSMD : TightCSMD p f :=
  fun _ _ _ _ _ _ ht => commutingSylowForcesCommuting_of_tightD (S19R.tightStd_of_tightBranchD ht)

theorem conjSubgroup_sylow_eq_of_tightD (ht : S19R.TightStd p f K z) (Q : Sylow 2 K)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hQS : (Q : Subgroup K).map K.subtype ≤ S) {g : G}
    (hgS : conjSubgroup g ((Q : Subgroup K).map K.subtype) ≤ S) :
    conjSubgroup g ((Q : Subgroup K).map K.subtype) = (Q : Subgroup K).map K.subtype := by
  have ht' := ht.toTightBranch
  have hU := uniqueInvolutionNormal_of_tight ht'
  have hQq := quaternion_sylow_of_isClassicalMember ht.branch.odd ht.branch.five
    ht.branch.member Q
  have hzQ : z ∈ (Q : Subgroup K).map K.subtype :=
    mem_of_isSylow2Of_of_tight ht' (isSylow2Of_map_subtype Q)
  by_contra hne
  have h1 : conjSubgroup 1 ((Q : Subgroup K).map K.subtype) ≤ S := by
    rw [conjSubgroup_one]
    exact hQS
  have hne' : conjSubgroup 1 ((Q : Subgroup K).map K.subtype) ≠
      conjSubgroup g ((Q : Subgroup K).map K.subtype) := by
    rw [conjSubgroup_one]
    exact fun h => hne h.symm
  obtain ⟨hbot, hcomm⟩ := quaternion_conjugates_commute Q hQq hzQ hU.1 hU.2.2.2.1 hU.2.2.2.2 hS
    hQS h1 hgS hne'
  rw [conjSubgroup_one] at hbot hcomm
  by_cases hg : g ∈ Subgroup.normalizer (K : Set G)
  ·
    have hgz : g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [← normalizer_eq_centralizer_of_tight ht']
      exact hg
    have hz' : z ∈ conjSubgroup g ((Q : Subgroup K).map K.subtype) := by
      have h := mem_conjSubgroup_of_mem (g := g) hzQ
      rwa [show g * z * g⁻¹ = z by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hgz]; group] at h
    have hz1 : z ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_inf.mpr ⟨hzQ, hz'⟩
    rw [Subgroup.mem_bot] at hz1
    have h2 := hU.1
    rw [hz1] at h2
    simp at h2
  · exact absurd (Or.inl (mem_omegaNbr_of_commuting_sylow ht' hg (isSylow2Of_map_subtype Q)
      ((isSylow2Of_map_subtype Q).conj g) hcomm))
      (ht.edgeless K (CoreAssembly.mem_conjClass_self K) _ ⟨g, rfl⟩)

end CFSG.ClassicalInvolution.Disconnected.AschTight
