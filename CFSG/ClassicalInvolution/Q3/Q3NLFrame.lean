module

public import CFSG.ClassicalInvolution.Q3.Q3NLExact
public import CFSG.ClassicalInvolution.Q3.Q3PBranch

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement MatrixGroups

section Frame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

@[expose] def FuzzyFrame3 (Ω : Set (Subgroup G)) (A : Subgroup G) : Prop :=
  ∃ (J : Fin 3 → Subgroup G) (z : Fin 3 → G),
    (∀ i, J i ∈ Ω ∧ IsClassicalMember3 (J i) (z i)) ∧ A = Subgroup.closure (Set.range z) ∧
      IsElemAbelian 2 A ∧ Nat.card A = 8 ∧ ∀ i, A ≤ trivialOnQuot (J i)

@[expose] def fuzzyVertices3 (Ω : Set (Subgroup G)) (A : Subgroup G) : Set G :=
  {z | z ∈ A ∧ ∃ J ∈ Ω, IsClassicalMember3 J z ∧ A ≤ trivialOnQuot J}

theorem FuzzyFrame3.exists_vertex (h : FuzzyFrame3 Ω A) : ∃ z, z ∈ fuzzyVertices3 Ω A := by
  obtain ⟨J, z, hJ, hA, -, -, htriv⟩ := h
  exact ⟨z 0, hA ▸ Subgroup.subset_closure ⟨0, rfl⟩, J 0, (hJ 0).1, (hJ 0).2, htriv 0⟩

theorem isPGroup_zpowers_of_mem_isElemAbelian3 {B : Subgroup G} (hB : IsElemAbelian 2 B) {c : G}
    (hc : c ∈ B) : IsPGroup 2 (Subgroup.zpowers c) := by
  have hsq : c * c = 1 := by simpa only [pow_two] using hB.2 c hc
  refine isPGroup_two_of_sq_eq_one fun x hx => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← (Commute.refl c).mul_zpow, hsq, one_zpow]

theorem IndepTriple3.fuzzyFrame3 (h : IndepTriple3 Ω) : ∃ A : Subgroup G, FuzzyFrame3 Ω A := by
  obtain ⟨K, z, hmem, hcomm, hA, hcard⟩ := h
  refine ⟨Subgroup.closure (Set.range z), K, z, hmem, rfl, hA, hcard, fun i => ?_⟩
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨j, rfl⟩
  refine mem_trivialOnQuot_of_centralizes fun x hx => ?_
  by_cases hji : j = i
  · subst hji
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (isSubnormal_le (hmem j).2.subnormal hx)).symm
  · exact (hcomm i j (Ne.symm hji) x hx _ (hmem j).2.mem).symm

theorem FuzzyFrame3.conj (hΩ : ConjInvariant Ω) (h : FuzzyFrame3 Ω A) (g : G) :
    FuzzyFrame3 Ω (conjSub g A) := by
  obtain ⟨J, z, hJ, hA, hAe, hAc, hAt⟩ := h
  refine ⟨fun i => conjSub g (J i), fun i => g * z i * g⁻¹,
    fun i => ⟨hΩ g _ (hJ i).1, (hJ i).2.conj g⟩, ?_,
    Balance.BootRank3.isElemAbelian_two_conjSub hAe g, ?_, fun i x hx => ?_⟩
  · rw [hA]
    show Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.closure (Set.range z)) = _
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  · have h1 := Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective
    rw [← hAc]
    exact h1
  · have hx' := mem_conjSub_iff.mp hx
    have h2 := trivialOnQuot_conjSub (hAt i hx') g
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h2


end Frame

section Vertex

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem FuzzyFrame3.mem_tqMembers3 (h : FuzzyFrame3 Ω A) :
    ∃ J : Fin 3 → Subgroup G, ∃ z : Fin 3 → G, (∀ i, J i ∈ Ω ∧ IsClassicalMember3 (J i) (z i)) ∧
      A = Subgroup.closure (Set.range z) ∧ ∀ a ∈ A, ∀ i, J i ∈ tqMembers3 Ω a := by
  obtain ⟨J, z, hJ, hA, -, -, htriv⟩ := h
  exact ⟨J, z, hJ, hA, fun a ha i => ⟨(hJ i).1, htriv i ha⟩⟩

theorem FuzzyFrame3.exactCore3_mem_exactFamily3 (h : FuzzyFrame3 Ω A) :
    ∃ J : Fin 3 → Subgroup G, ∃ z : Fin 3 → G, (∀ i, J i ∈ Ω ∧ IsClassicalMember3 (J i) (z i)) ∧
      A = Subgroup.closure (Set.range z) ∧
      ∀ a ∈ A, ∀ i, exactCore3 a (J i) ∈ exactFamily3 Ω a := by
  obtain ⟨J, z, hJ, hA, htq⟩ := h.mem_tqMembers3
  exact ⟨J, z, hJ, hA, fun a ha i => Q3NL.exactCore3_mem_exactFamily3 (htq a ha i)⟩

theorem FuzzyFrame3.isSectionMember3_exactCore3 {J : Subgroup G} {z a : G}
    (hA : IsElemAbelian 2 A) (ha : a ∈ A) (hJ : IsClassicalMember3 J z)
    (hAJ : A ≤ trivialOnQuot J) :
    IsSectionMember3 (Subgroup.centralizer ({a} : Set G)) (exactCore3 a J) z :=
  Q3NL.isSectionMember3_exactCore3 hJ (isPGroup_zpowers_of_mem_isElemAbelian3 hA ha) (hAJ ha)

theorem FuzzyFrame3.le_trivialOnQuot_exactCore3 {J : Subgroup G} {z a : G}
    (hA : IsElemAbelian 2 A) (ha : a ∈ A) (hJ : IsClassicalMember3 J z) (hAJ : A ≤ trivialOnQuot J)
    {B : Subgroup G} (hBA : B ≤ A) (hBa : B ≤ Subgroup.centralizer ({a} : Set G)) :
    B ≤ trivialOnQuot (exactCore3 a J) :=
  Q3NL.le_trivialOnQuot_exactCore3 hJ (isPGroup_zpowers_of_mem_isElemAbelian3 hA ha) (hAJ ha) hBa
    (hBA.trans hAJ)

end Vertex

end CFSG.ClassicalInvolution.Q3.Q3NL
