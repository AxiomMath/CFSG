module

public import CFSG.FeitThompson.Definitions.LocalTypesIIThroughV
import CFSG.FeitThompson.OddOrder.LocalTypesConjugationInvariant
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G] {M E E' W₁ W₂ W₁' W₂' : Subgroup G}

omit [Finite G] in
private theorem conj_smul_eq_map_conj_aux {X : Type*} [Group X] (g : X) (S : Subgroup X) :
    MulAut.conj g • S = S.map (MulAut.conj g : X →* X) := by
  rw [Subgroup.pointwise_smul_def]
  rfl

omit [Finite G] in
private theorem map_subtype_map_conj {K : Subgroup G} (r : K) (S : Subgroup K) :
    (S.map (MulAut.conj r : K →* K)).map K.subtype
      = (S.map K.subtype).map (MulAut.conj (r : G) : G →* G) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
private theorem map_conj_eq_self {A : Subgroup G} {g : G} (hg : g ∈ A) :
    A.map (MulAut.conj g : G →* G) = A :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hg)

omit [Finite G] in
private theorem normalizer_map_conj_le_iff {A B : Subgroup G} {g : G} (hgB : g ∈ B) :
    normalizer ((A.map (MulAut.conj g : G →* G) : Subgroup G) : Set G) ≤ B ↔
      normalizer (A : Set G) ≤ B := by
  rw [← map_normalizer_coe (MulAut.conj g) A]
  constructor
  · intro h x hx
    have hb : MulAut.conj g x ∈ B := h (Subgroup.mem_map_of_mem _ hx)
    simpa [MulAut.conj_apply, mul_assoc] using
      B.mul_mem (B.mul_mem (B.inv_mem hgB) hb) hgB
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa [MulAut.conj_apply] using B.mul_mem (B.mul_mem hgB (h hx)) (B.inv_mem hgB)

omit [Finite G] in
private theorem isSolvable_commutator_of_isSolvable {M : Subgroup G} (h : Group.IsSolvable M) :
    Group.IsSolvable (⁅M, M⁆ : Subgroup G) := by
  have := h
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (Subgroup.commutator_le_self M))

namespace IsWitnessedPConfiguration

theorem natCard_E_eq (hc : IsWitnessedPConfiguration M E W₁ W₂)
    (hc' : IsWitnessedPConfiguration M E' W₁' W₂') : Nat.card E = Nat.card E' :=
  Nat.eq_of_mul_eq_mul_left Nat.card_pos
    (hc.natCard_commutator_eq.symm.trans hc'.natCard_commutator_eq)

theorem natCard_W₁_eq (hc : IsWitnessedPConfiguration M E W₁ W₂)
    (hc' : IsWitnessedPConfiguration M E' W₁' W₂') : Nat.card W₁ = Nat.card W₁' :=
  Nat.eq_of_mul_eq_mul_left (n := Nat.card (⁅M, M⁆ : Subgroup G)) Nat.card_pos
    (hc.natCard_M_eq.symm.trans hc'.natCard_M_eq)

theorem coprime_natCard_hallCore_natCard_E (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    (Nat.card ((hallCore M).map M.subtype)).Coprime (Nat.card E) := by
  have hmap : Nat.card ((hallCore ↥M).map M.subtype) = Nat.card (hallCore ↥M) :=
    Subgroup.card_map_of_injective M.subtype_injective
  have h2 : Nat.card (hallCore ↥M) * (hallCore ↥M).index
      = Nat.card (hallCore ↥M) * (Nat.card E * Nat.card W₁) := by
    rw [Subgroup.card_mul_index, hc.natCard_M_eq, hc.natCard_commutator_eq, hmap, mul_assoc]
  have hcop := coprime_natCard_index_hallCore (X := ↥M)
  rw [Nat.eq_of_mul_eq_mul_left Nat.card_pos h2] at hcop
  rw [hmap]
  exact hcop.coprime_dvd_right (dvd_mul_right _ _)

theorem isHallSubgroup_subgroupOf_E (hc : IsWitnessedPConfiguration M E W₁ W₂) {n : ℕ}
    (hn : Nat.card E = n) :
    IsHallSubgroup (n.primeFactors : Set ℕ) (E.subgroupOf (⁅M, M⁆ : Subgroup G)) := by
  have hcardE : Nat.card (E.subgroupOf (⁅M, M⁆ : Subgroup G)) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.le_commutator_E).toEquiv
  have hindex : (E.subgroupOf (⁅M, M⁆ : Subgroup G)).index
      = Nat.card ((hallCore M).map M.subtype) := by
    have h := hc.isComplement'_subgroupOf_hallCore_E.index_eq_card
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.hallCore_le_commutator).toEquiv] at h
  refine isHallSubgroup_iff.2 ⟨?_, ?_⟩
  · rw [isPiNumber_iff, hcardE, hn]
    exact fun p hp => by simpa using hp
  · rw [isPiNumber_iff, hindex]
    intro p hp
    have hdisj := hc.coprime_natCard_hallCore_natCard_E.disjoint_primeFactors
    simp only [Set.mem_compl_iff, Finset.mem_coe, ← hn]
    exact Finset.disjoint_left.1 hdisj hp

theorem exists_mem_commutator_map_conj_eq (hc : IsWitnessedPConfiguration M E W₁ W₂)
    (hc' : IsWitnessedPConfiguration M E' W₁' W₂')
    (hsolv : Group.IsSolvable (⁅M, M⁆ : Subgroup G)) :
    ∃ g ∈ (⁅M, M⁆ : Subgroup G), E'.map (MulAut.conj g : G →* G) = E := by
  have := hsolv
  obtain ⟨x, hx⟩ := exists_conj_smul_eq_of_isHallSubgroup
    (hc'.isHallSubgroup_subgroupOf_E (hc'.natCard_E_eq hc))
    (hc.isHallSubgroup_subgroupOf_E rfl)
  refine ⟨(x : G), x.2, ?_⟩
  have h := congrArg (Subgroup.map (⁅M, M⁆ : Subgroup G).subtype) hx
  rwa [conj_smul_eq_map_conj_aux, map_subtype_map_conj,
    Subgroup.map_subgroupOf_eq_of_le hc'.le_commutator_E,
    Subgroup.map_subgroupOf_eq_of_le hc.le_commutator_E] at h

end IsWitnessedPConfiguration

theorem IsPConfigurationIIToIV.of_isWitnessedPConfiguration
    (hc0 : IsPConfigurationIIToIV M E' W₁' W₂')
    (hc : IsWitnessedPConfiguration M E W₁ W₂) : IsPConfigurationIIToIV M E W₁ W₂ where
  isWitnessedPConfiguration := hc
  prime_natCard_W₁ := by
    rw [hc.natCard_W₁_eq hc0.isWitnessedPConfiguration]; exact hc0.prime_natCard_W₁
  isTIWithNormalizer_fittingRawSharp := hc0.isTIWithNormalizer_fittingRawSharp

theorem IsTypeII.clauses_of_isWitnessedPConfiguration (h : IsTypeII M)
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    IsPConfigurationIIToIV M E W₁ W₂ ∧ E ≠ ⊥ ∧ IsMulCommutative E ∧
      ¬ normalizer (E : Set G) ≤ M ∧
      IsFrobeniusType ↥(⁅M, M⁆ : Subgroup G) (E.subgroupOf (⁅M, M⁆ : Subgroup G)) ∧
      (hallCore ↥(⁅M, M⁆ : Subgroup G)).map (⁅M, M⁆ : Subgroup G).subtype =
        (hallCore M).map M.subtype := by
  obtain ⟨E', W₁', W₂', hc0, hE', habel', hnorm', hfrob', hhall⟩ :=
    h.exists_isPConfigurationIIToIV
  obtain ⟨g, hg, hgE⟩ := hc.exists_mem_commutator_map_conj_eq hc0.isWitnessedPConfiguration
    (isSolvable_commutator_of_isSolvable hsolv)
  have hgM : g ∈ M := Subgroup.commutator_le_self M hg
  have hMconj : (⁅M, M⁆ : Subgroup G).map (MulAut.conj g : G →* G) = ⁅M, M⁆ :=
    map_conj_eq_self hg
  refine ⟨hc0.of_isWitnessedPConfiguration hc, ?_, ?_, ?_, ?_, hhall⟩
  · rw [← hgE, Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]; exact hE'
  · have := habel'; rw [← hgE]; exact Subgroup.map_isMulCommutative _ _
  · rw [← hgE, normalizer_map_conj_le_iff hgM]; exact hnorm'
  · rw [← hgE]; exact isFrobeniusType_map_subgroupOf_of_eq (MulAut.conj g) hMconj hfrob'

theorem IsTypeII.clauses_of_isWitnessedPConfiguration_of_minimalSimple
    (_hsimple : IsSimpleGroup G) (_hna : ¬ IsMulCommutative G) (_hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K) (hM : IsCoatom M) (h : IsTypeII M)
    (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    IsPConfigurationIIToIV M E W₁ W₂ ∧ E ≠ ⊥ ∧ IsMulCommutative E ∧
      ¬ normalizer (E : Set G) ≤ M ∧
      IsFrobeniusType ↥(⁅M, M⁆ : Subgroup G) (E.subgroupOf (⁅M, M⁆ : Subgroup G)) ∧
      (hallCore ↥(⁅M, M⁆ : Subgroup G)).map (⁅M, M⁆ : Subgroup G).subtype =
        (hallCore M).map M.subtype :=
  h.clauses_of_isWitnessedPConfiguration (hsolv M hM.1) hc

theorem IsTypeIII.clauses_of_isWitnessedPConfiguration (h : IsTypeIII M)
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    IsPConfigurationIIToIV M E W₁ W₂ ∧ E ≠ ⊥ ∧ IsMulCommutative E ∧
      normalizer (E : Set G) ≤ M := by
  obtain ⟨E', W₁', W₂', hc0, hE', habel', hnorm'⟩ := h.exists_isPConfigurationIIToIV
  obtain ⟨g, hg, hgE⟩ := hc.exists_mem_commutator_map_conj_eq hc0.isWitnessedPConfiguration
    (isSolvable_commutator_of_isSolvable hsolv)
  have hgM : g ∈ M := Subgroup.commutator_le_self M hg
  refine ⟨hc0.of_isWitnessedPConfiguration hc, ?_, ?_, ?_⟩
  · rw [← hgE, Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]; exact hE'
  · have := habel'; rw [← hgE]; exact Subgroup.map_isMulCommutative _ _
  · rw [← hgE, normalizer_map_conj_le_iff hgM]; exact hnorm'

theorem IsTypeIII.clauses_of_isWitnessedPConfiguration_of_minimalSimple
    (_hsimple : IsSimpleGroup G) (_hna : ¬ IsMulCommutative G) (_hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K) (hM : IsCoatom M) (h : IsTypeIII M)
    (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    IsPConfigurationIIToIV M E W₁ W₂ ∧ E ≠ ⊥ ∧ IsMulCommutative E ∧
      normalizer (E : Set G) ≤ M :=
  h.clauses_of_isWitnessedPConfiguration (hsolv M hM.1) hc

theorem IsTypeIV.clauses_of_isWitnessedPConfiguration (h : IsTypeIV M)
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    IsPConfigurationIIToIV M E W₁ W₂ ∧ ¬ IsMulCommutative E ∧
      normalizer (E : Set G) ≤ M := by
  obtain ⟨E', W₁', W₂', hc0, habel', hnorm'⟩ := h.exists_isPConfigurationIIToIV
  obtain ⟨g, hg, hgE⟩ := hc.exists_mem_commutator_map_conj_eq hc0.isWitnessedPConfiguration
    (isSolvable_commutator_of_isSolvable hsolv)
  have hgM : g ∈ M := Subgroup.commutator_le_self M hg
  refine ⟨hc0.of_isWitnessedPConfiguration hc, ?_, ?_⟩
  · exact fun hcm =>
      habel' (isMulCommutative_of_map_isMulCommutative (MulAut.conj g) (hgE ▸ hcm))
  · rw [← hgE, normalizer_map_conj_le_iff hgM]; exact hnorm'

theorem IsTypeIV.clauses_of_isWitnessedPConfiguration_of_minimalSimple
    (_hsimple : IsSimpleGroup G) (_hna : ¬ IsMulCommutative G) (_hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K) (hM : IsCoatom M) (h : IsTypeIV M)
    (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    IsPConfigurationIIToIV M E W₁ W₂ ∧ ¬ IsMulCommutative E ∧
      normalizer (E : Set G) ≤ M :=
  h.clauses_of_isWitnessedPConfiguration (hsolv M hM.1) hc

theorem IsTypeV.clauses_of_isWitnessedPConfiguration (h : IsTypeV M)
    (hsolv : Group.IsSolvable M) (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    E = ⊥ ∧
      (IsTIWithNormalizer (hallCoreSharp M) M ∨
        (∃ r ∈ (Nat.card (hallCore M)).primeFactors,
          IsCyclic (pComplCore r (hallCore M)) ∧ Nat.card W₁ ∣ r - 1) ∨
        (∃ r ∈ (Nat.card (hallCore M)).primeFactors,
          IsCyclic (pComplCore r (hallCore M)) ∧
            Nat.card (pCore r (hallCore M)) = r ^ 3 ∧ Nat.card W₁ ∣ r + 1)) := by
  obtain ⟨W₁', W₂', hc0, halt⟩ := h.exists_isWitnessedPConfiguration
  obtain ⟨g, -, hgE⟩ :=
    hc.exists_mem_commutator_map_conj_eq hc0 (isSolvable_commutator_of_isSolvable hsolv)
  refine ⟨by rw [← hgE, Subgroup.map_bot], ?_⟩
  rw [hc.natCard_W₁_eq hc0]
  exact halt

theorem IsTypeV.clauses_of_isWitnessedPConfiguration_of_minimalSimple
    (_hsimple : IsSimpleGroup G) (_hna : ¬ IsMulCommutative G) (_hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K) (hM : IsCoatom M) (h : IsTypeV M)
    (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    E = ⊥ ∧
      (IsTIWithNormalizer (hallCoreSharp M) M ∨
        (∃ r ∈ (Nat.card (hallCore M)).primeFactors,
          IsCyclic (pComplCore r (hallCore M)) ∧ Nat.card W₁ ∣ r - 1) ∨
        (∃ r ∈ (Nat.card (hallCore M)).primeFactors,
          IsCyclic (pComplCore r (hallCore M)) ∧
            Nat.card (pCore r (hallCore M)) = r ^ 3 ∧ Nat.card W₁ ∣ r + 1)) :=
  h.clauses_of_isWitnessedPConfiguration (hsolv M hM.1) hc

end

end CFSG.FeitThompson
