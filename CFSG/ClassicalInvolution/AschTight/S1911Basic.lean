module

public import CFSG.ClassicalInvolution.AschTight.OmegaD

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem exists_isUniqueInvolution_member (ht : S19R.TightStdDelta p f K z) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K) : ∃ u : G, IsUniqueInvolution J u := by
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
  exact ⟨_, (isUniqueInvolution_of_tight ht).conj g⟩

theorem eq_of_isUniqueInvolution_member (ht : S19R.TightStdDelta p f K z) {J₁ J₂ : Subgroup G}
    (h₁ : J₁ ∈ CoreAssembly.conjClass K) (h₂ : J₂ ∈ CoreAssembly.conjClass K) {u : G}
    (hu₁ : IsUniqueInvolution J₁ u) (hu₂ : IsUniqueInvolution J₂ u) : J₁ = J₂ := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class K J₁ h₁
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K J₂ h₂
  have hI := isUniqueInvolution_of_tight ht
  have ha := (hI.conj a).eq hu₁
  have hb := (hI.conj b).eq hu₂
  exact conjSub_eq_conjSub_of_tight ht (ha.trans hb.symm)

theorem centralizer_le_normalizer_member (ht : S19R.TightStdDelta p f K z) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K) {u : G} (hu : IsUniqueInvolution J u) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  intro v hv
  refine mem_normalizer_of_commute_of_tight ht hJ hu ?_
  exact (Subgroup.mem_centralizer_singleton_iff.mp hv).symm.symm

omit [Finite G] in
theorem normalizer_le_centralizer_member {J : Subgroup G} {u : G} (hu : IsUniqueInvolution J u) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := hu.conj_eq (conjSub_eq_of_mem_normalizer hn)
  calc n * u = n * u * n⁻¹ * n := by group
    _ = u * n := by rw [h1]

theorem normalizer_eq_centralizer_member (ht : S19R.TightStdDelta p f K z) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K) {u : G} (hu : IsUniqueInvolution J u) :
    Subgroup.normalizer (J : Set G) = Subgroup.centralizer ({u} : Set G) :=
  le_antisymm (normalizer_le_centralizer_member hu) (centralizer_le_normalizer_member ht hJ hu)

omit [Finite G] in
theorem not_le_normalizer_of_mem_rSet (hD : DEdgeless (CoreAssembly.conjClass K))
    {J₁ J₂ : Subgroup G} (h₁ : J₁ ∈ CoreAssembly.conjClass K) (h₂ : J₂ ∈ CoreAssembly.conjClass K)
    (hne : J₁ ≠ J₂) {R₁ : Subgroup G} (hR₁ : R₁ ∈ RSet (CoreAssembly.conjClass K))
    (hR₁J : R₁ ≤ J₁) : ¬ R₁ ≤ Subgroup.normalizer (J₂ : Set G) := by
  intro hN
  exact hD J₂ h₂ J₁ h₁ (Or.inl ⟨h₁, hne, R₁, hR₁, hR₁J, hN⟩)

theorem not_le_centralizer_of_mem_rSet (ht : S19R.TightStd p f K z) {J₁ J₂ : Subgroup G}
    (h₁ : J₁ ∈ CoreAssembly.conjClass K) (h₂ : J₂ ∈ CoreAssembly.conjClass K) (hne : J₁ ≠ J₂)
    {u : G} (hu : IsUniqueInvolution J₂ u) {R₁ : Subgroup G}
    (hR₁ : R₁ ∈ RSet (CoreAssembly.conjClass K)) (hR₁J : R₁ ≤ J₁) :
    ¬ R₁ ≤ Subgroup.centralizer ({u} : Set G) := fun hC =>
  not_le_normalizer_of_mem_rSet ht.edgeless h₁ h₂ hne hR₁ hR₁J
    (hC.trans (centralizer_le_normalizer_member ht.toTightBranch h₂ hu))

theorem mem_of_le_member {J A : Subgroup G} {u : G} (hu : IsUniqueInvolution J u) (hAJ : A ≤ J)
    (hA : IsPGroup 2 A) (h2 : 2 ≤ Nat.card A) : u ∈ A :=
  AscL62.mem_of_uniqueInvolution_of_pGroup hu hAJ hA h2

omit [Finite G] in
theorem eq_of_mem_member {J A : Subgroup G} {u : G} (hu : IsUniqueInvolution J u) (hAJ : A ≤ J)
    {x : G} (hx : x ∈ A) (hx2 : x * x = 1) (hx1 : x ≠ 1) : x = u :=
  (hu.unique x (hAJ hx) hx2).resolve_left hx1

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
