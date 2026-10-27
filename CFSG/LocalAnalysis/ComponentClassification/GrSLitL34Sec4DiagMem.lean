module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement Pointwise

section InGroup

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_normalizer_sup_of_mem {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem not_mem_sup_conjugate_of_ne {K : Subgroup X} {a : X} (hK : IsPComponent 2 K)
    (hne : conjugate K a ≠ K) : a ∉ K ⊔ conjugate K a ⊔ pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro haN
  set K₂ : Subgroup X := conjugate K a with hK₂
  set O : Subgroup X := pPrimeCore 2 X with hO
  have hOn : O.Normal := pPrimeCore_normal
  have hON : ∀ g : X, g ∈ normalizer (O : Set X) := fun g => by
    rw [normalizer_eq_top_iff.mpr hOn]
    exact mem_top g
  have hK₂c : IsPComponent 2 K₂ :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (MulAut.conj a⁻¹) hK
  obtain ⟨h21, -, hcomm⟩ :=
    CatalogueBPrimeJoin.mutual_normalization_core_commutation 2 K K₂ hK hK₂c (Ne.symm hne)
  have hle : K ⊔ K₂ ⊔ O ≤ normalizer ((K ⊔ O : Subgroup X) : Set X) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_sup_left.trans le_normalizer
    · exact fun k hk => mem_normalizer_sup_of_mem (h21 hk) (hON k)
    · exact le_sup_right.trans le_normalizer
  have haKO : a⁻¹ ∈ normalizer ((K ⊔ O : Subgroup X) : Set X) := inv_mem (hle haN)
  have hOa : O.map (MulAut.conj a⁻¹).toMonoidHom = O :=
    mem_normalizer_iff_map_conj_eq.mp (hON a⁻¹)
  have hKO : K ≤ K₂ ⊔ O := by
    have h1 : (K ⊔ O).map (MulAut.conj a⁻¹).toMonoidHom = K ⊔ O :=
      mem_normalizer_iff_map_conj_eq.mp haKO
    rw [Subgroup.map_sup, hOa] at h1
    rw [hK₂, conjugate, h1]
    exact le_sup_left
  have hOK : (pPrimeCore 2 ↥K).map K.subtype ≤ O :=
    Walter.map_pPrimeCore_le_of_isSubnormal hK.choose_spec.2.1
  have hKK : ⁅K, K⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    have hh' : h ∈ (K₂ : Set X) * (O : Set X) := by
      rw [← Subgroup.mul_normal K₂ O]
      exact hKO hh
    obtain ⟨k, hk, o, ho, rfl⟩ := hh'
    have e : ⁅g, k * o⁆ = ⁅g, k⁆ * (k * (g * o * g⁻¹ * o⁻¹) * k⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine mul_mem (hOK (mem_inf.mp (hcomm (commutator_mem_commutator hg hk))).1) ?_
    exact hOn.conj_mem _ (mul_mem (hOn.conj_mem o ho g) (inv_mem ho)) k
  have hperf : ⁅K, K⁆ = K :=
    Subgroup.isPerfect_iff.mp (CatalogueBHeldSmallCore.pComponent_perfect 2 K hK)
  have hKle : K ≤ O := hperf ▸ hKK
  obtain ⟨C, hC, -, hmap, -⟩ := hK
  have hbot : K.map (QuotientGroup.mk' (pPrimeCore 2 X)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hKle
  rw [hmap] at hbot
  subst hbot
  obtain ⟨x, y, hxy⟩ := (LocalCores.isQuasisimple_nontrivial hC.1).exists_pair_ne
  exact hxy (Subsingleton.elim x y)

end InGroup

variable {G : Type} [Group G] [Finite G]

theorem not_mem_sup_conjugate_subgroupOf {M K : Subgroup G} {a : G} (hKM : K ≤ M)
    (hKc : IsPComponent 2 (K.subgroupOf M)) (haM : a ∈ M) (hne : conjugate K a ≠ K) :
    a ∉ K ⊔ conjugate K a ⊔ oddIn M := by
  intro h
  have hne' : conjugate (K.subgroupOf M) ⟨a, haM⟩ ≠ K.subgroupOf M := by
    intro h1
    apply hne
    have h2 := congrArg (map M.subtype) h1
    rwa [map_conjugate_subtype, map_subgroupOf_subtype hKM] at h2
  apply not_mem_sup_conjugate_of_ne hKc hne'
  have hmap : (K.subgroupOf M ⊔ conjugate (K.subgroupOf M) ⟨a, haM⟩ ⊔
      pPrimeCore 2 ↥M).map M.subtype = K ⊔ conjugate K a ⊔ oddIn M := by
    rw [Subgroup.map_sup, Subgroup.map_sup, map_conjugate_subtype, map_subgroupOf_subtype hKM]
    rfl
  rw [← hmap] at h
  obtain ⟨y, hy, hya⟩ := mem_map.mp h
  have hy' : y = ⟨a, haM⟩ := Subtype.ext hya
  rwa [hy'] at hy

theorem diagonal_false_of_mem {M K J : Subgroup G} {a : G} (hKM : K ≤ M)
    (hKc : IsPComponent 2 (K.subgroupOf M)) (haM : a ∈ M) (hne : conjugate K a ≠ K)
    (hJK : J ≤ K ⊔ conjugate K a ⊔ oddIn M) (haJ : a ∈ J) : False :=
  not_mem_sup_conjugate_subgroupOf hKM hKc haM hne (hJK haJ)

end CFSG.ComponentClassification.GrSLit.GrS4
