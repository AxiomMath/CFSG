module

public import CFSG.FeitThompson.Definitions.LocalTypesIIThroughV
import CFSG.FeitThompson.OddOrder.LocalTypesConjugationInvariant
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G]

theorem isComplement'_subgroupOf_commutator_of_sup_of_disjoint {M W : Subgroup G}
    (hsup : ⁅M, M⁆ ⊔ W = M) (hdisj : Disjoint (⁅M, M⁆ : Subgroup G) W) :
    ((⁅M, M⁆ : Subgroup G).subgroupOf M).IsComplement' (W.subgroupOf M) := by
  have hWM : W ≤ M := hsup ▸ le_sup_right
  have := normal_subgroupOf_commutator_self M
  refine (isComplement'_of_sup_eq_top_of_inf_eq_bot ?_ ?_).symm
  · rw [← Subgroup.subgroupOf_sup (Subgroup.commutator_le_self M) hWM, hsup,
      Subgroup.subgroupOf_self]
  · rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, disjoint_iff.1 hdisj]
    simp

private theorem natCard_subgroupOf_eq_of_le {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem relIndex_eq_natCard_commutator_of_sup_of_disjoint {M W : Subgroup G}
    (hsup : ⁅M, M⁆ ⊔ W = M) (hdisj : Disjoint (⁅M, M⁆ : Subgroup G) W) :
    W.relIndex M = Nat.card (⁅M, M⁆ : Subgroup G) := by
  have h := (isComplement'_subgroupOf_commutator_of_sup_of_disjoint hsup hdisj).index_eq_card
  rwa [natCard_subgroupOf_eq_of_le (Subgroup.commutator_le_self M)] at h

theorem natCard_eq_mul_of_sup_of_disjoint {M W : Subgroup G}
    (hsup : ⁅M, M⁆ ⊔ W = M) (hdisj : Disjoint (⁅M, M⁆ : Subgroup G) W) :
    Nat.card M = Nat.card (⁅M, M⁆ : Subgroup G) * Nat.card W := by
  have hWM : W ≤ M := hsup ▸ le_sup_right
  have h := (isComplement'_subgroupOf_commutator_of_sup_of_disjoint hsup hdisj).card_mul_card
  rwa [natCard_subgroupOf_eq_of_le (Subgroup.commutator_le_self M),
    natCard_subgroupOf_eq_of_le hWM, eq_comm] at h

theorem isHallSubgroup_subgroupOf_primeFactors {M W : Subgroup G} (hWM : W ≤ M)
    (h : (Nat.card W).Coprime (W.relIndex M)) :
    IsHallSubgroup ((Nat.card W).primeFactors : Set ℕ) (W.subgroupOf M) := by
  rw [isHallSubgroup_iff]
  refine ⟨?_, ?_⟩
  · rw [isPiNumber_iff, natCard_subgroupOf_eq_of_le hWM]
    exact fun p hp => hp
  · rw [isPiNumber_iff]
    intro p hp
    have hp1 : p ∣ W.relIndex M := Nat.dvd_of_mem_primeFactors hp
    simp only [Set.mem_compl_iff, Finset.mem_coe]
    intro hmem
    exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne'
      (Nat.eq_one_of_dvd_one (h ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hmem) hp1))

theorem map_conj_eq_of_map_conj_subgroupOf {M A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M)
    {g : M} (h : (A.subgroupOf M).map ((MulAut.conj g : M ≃* M) : M →* M) = B.subgroupOf M) :
    A.map ((MulAut.conj (g : G) : G ≃* G) : G →* G) = B := by
  have hcomp : (M.subtype).comp ((MulAut.conj g : M ≃* M) : M →* M)
      = ((MulAut.conj (g : G) : G ≃* G) : G →* G).comp M.subtype := by
    ext x; simp [MulAut.conj_apply]
  have hmap := congrArg (fun S : Subgroup M => S.map M.subtype) h
  simp only [Subgroup.map_map, hcomp] at hmap
  rwa [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hA, inf_eq_left.2 hB] at hmap

variable [Finite G]

theorem exists_mem_map_conj_eq_and_isWitnessedPConfiguration
    {M E₀ V₁ V₂ W₁ : Subgroup G} [Group.IsSolvable M]
    (hc : IsWitnessedPConfiguration M E₀ V₁ V₂)
    (hsup : ⁅M, M⁆ ⊔ W₁ = M) (hdisj : Disjoint (⁅M, M⁆ : Subgroup G) W₁) :
    ∃ y ∈ M, V₁.map (MulAut.conj y⁻¹ : G →* G) = W₁ ∧
      IsWitnessedPConfiguration M (E₀.map (MulAut.conj y⁻¹ : G →* G)) W₁
        (V₂.map (MulAut.conj y⁻¹ : G →* G)) := by
  have hWM : W₁ ≤ M := hsup ▸ le_sup_right
  have hcard : Nat.card W₁ = Nat.card V₁ :=
    Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (⁅M, M⁆ : Subgroup G)))
      ((natCard_eq_mul_of_sup_of_disjoint hsup hdisj).symm.trans hc.natCard_M_eq)
  have hidx : W₁.relIndex M = V₁.relIndex M := by
    rw [relIndex_eq_natCard_commutator_of_sup_of_disjoint hsup hdisj,
      hc.relIndex_W₁_eq_natCard_commutator]
  have hWhall : (Nat.card W₁).Coprime (W₁.relIndex M) := by
    rw [hcard, hidx]; exact hc.hall_W₁
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_isHallSubgroup
    (isHallSubgroup_subgroupOf_primeFactors hc.le_M_W₁ hc.hall_W₁)
    (hcard ▸ isHallSubgroup_subgroupOf_primeFactors hWM hWhall)
  have hmap : V₁.map ((MulAut.conj (g : G) : G ≃* G) : G →* G) = W₁ :=
    map_conj_eq_of_map_conj_subgroupOf hc.le_M_W₁ hWM hg
  have hconj := hc.conj (g : G)⁻¹
  rw [inv_inv, show M.map (MulAut.conj (g : G) : G →* G) = M from
    Subgroup.conj_smul_eq_self_of_mem g.2, hmap] at hconj
  exact ⟨(g : G)⁻¹, inv_mem g.2, by rw [inv_inv]; exact hmap, by rw [inv_inv]; exact hconj⟩

theorem exists_map_conj_eq_of_ambient_hypotheses (_hsimple : IsSimpleGroup G)
    (_hna : ¬ IsMulCommutative G) (_hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K) {M E₀ V₁ V₂ W₁ : Subgroup G}
    (_hM : IsCoatom M) (hc : IsWitnessedPConfiguration M E₀ V₁ V₂)
    (_hW₁M : W₁ ≤ M) (hsup : ⁅M, M⁆ ⊔ W₁ = M) (hdisj : Disjoint (⁅M, M⁆ : Subgroup G) W₁) :
    ∃ y ∈ M, V₁.map (MulAut.conj y⁻¹ : G →* G) = W₁ ∧
      IsWitnessedPConfiguration M (E₀.map (MulAut.conj y⁻¹ : G →* G)) W₁
        (V₂.map (MulAut.conj y⁻¹ : G →* G)) :=
  have := hsolv M hc.lt_top.ne
  exists_mem_map_conj_eq_and_isWitnessedPConfiguration hc hsup hdisj

theorem eq_of_isWitnessedPConfiguration_of_map_conj
    {M E₀ V₁ V₂ E W₁ W₂ : Subgroup G} [Group.IsSolvable M]
    (hc : IsWitnessedPConfiguration M E₀ V₁ V₂) (hc' : IsWitnessedPConfiguration M E W₁ W₂)
    (hsup : ⁅M, M⁆ ⊔ W₁ = M) (hdisj : Disjoint (⁅M, M⁆ : Subgroup G) W₁) :
    ∃ y ∈ M, V₁.map (MulAut.conj y⁻¹ : G →* G) = W₁ ∧
      V₂.map (MulAut.conj y⁻¹ : G →* G) = W₂ := by
  obtain ⟨y, hyM, hy₁, hy⟩ := exists_mem_map_conj_eq_and_isWitnessedPConfiguration hc hsup hdisj
  exact ⟨y, hyM, hy₁, hy.eq_of_eq_W₁ hc'⟩

theorem exists_mem_map_conj_eq_and_isPConfigurationIIToIV
    {M E₀ V₁ V₂ W₁ : Subgroup G} [Group.IsSolvable M]
    (hc : IsPConfigurationIIToIV M E₀ V₁ V₂)
    (hsup : ⁅M, M⁆ ⊔ W₁ = M) (hdisj : Disjoint (⁅M, M⁆ : Subgroup G) W₁) :
    ∃ y ∈ M, V₁.map (MulAut.conj y⁻¹ : G →* G) = W₁ ∧
      IsPConfigurationIIToIV M (E₀.map (MulAut.conj y⁻¹ : G →* G)) W₁
        (V₂.map (MulAut.conj y⁻¹ : G →* G)) := by
  obtain ⟨y, hyM, hy₁, hy⟩ := exists_mem_map_conj_eq_and_isWitnessedPConfiguration
    hc.isWitnessedPConfiguration hsup hdisj
  refine ⟨y, hyM, hy₁, hy, ?_, hc.isTIWithNormalizer_fittingRawSharp⟩
  rw [← hy₁, Subgroup.card_map_of_injective (MulAut.conj y⁻¹ : G ≃* G).injective]
  exact hc.prime_natCard_W₁

end

end CFSG.FeitThompson
