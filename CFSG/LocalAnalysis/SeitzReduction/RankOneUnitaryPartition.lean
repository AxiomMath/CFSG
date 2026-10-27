module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryFusion

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint CFSG.GH74.Uniqueness.Bender

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem partition_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    normalizer (szA L T t : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G) ∧
    (gmsRootConjugates (szA L T t) (zpowers t)).ncard = 2 ^ f ∧
    ∀ Q₁ Q₂ Z₁ Z₂ : gmsRootConjugates (szA L T t) (zpowers t), Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
      ∃ σ ∈ (gmsRootConjugateAction (szA L T t) (zpowers t)).range, σ Q₁ = Z₁ ∧ σ Q₂ = Z₂ := by
  have hD := h.partitionData_of_card_sylow hS2
  obtain ⟨-, hcardA₁, -⟩ := h.facts_of_card_sylow hS2
  exact ⟨hD.normalizer_le, hD.ncard_eq.trans hcardA₁, hD.two_transitive⟩

theorem action_eq_one_iff_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (l : normalizer (szA L T t : Set G)) :
    gmsRootConjugateAction (szA L T t) (zpowers t) l = 1 ↔
      (l : G) ∈ centralizer (szA L T t : Set G) :=
  (h.partitionData_of_card_sylow hS2).action_eq_one_iff l

theorem relIndex_centralizer_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    (centralizer ({t} : Set G)).relIndex (normalizer (szA L T t : Set G)) = 2 ^ f := by
  have hD := h.partitionData_of_card_sylow hS2
  obtain ⟨-, hΔ, -⟩ := h.partition_of_card_sylow hS2
  set N := normalizer (szA L T t : Set G) with hN
  set R₀ : gmsRootConjugates (szA L T t) (zpowers t) := ⟨zpowers t, SzPartitionData.zpowers_mem⟩
    with hR₀
  have hstab : MulAction.stabilizer N R₀ = (centralizer ({t} : Set G)).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro hn
      have h1 : ((n • R₀ : gmsRootConjugates (szA L T t) (zpowers t)) : Subgroup G) =
          zpowers t := by rw [hn]
      exact (hD.map_conj_zpowers_eq_iff n).mp h1
    · intro hn
      exact Subtype.ext ((hD.map_conj_zpowers_eq_iff n).mpr hn)
  have horbit : MulAction.orbit N R₀ = Set.univ := by
    refine Set.eq_univ_of_forall fun Q => ?_
    obtain ⟨l, hl⟩ := hD.exists_smul_eq_zpowers Q
    let l' : N := ⟨l.1, l.2⟩
    have hlQ : l' • Q = R₀ := Subtype.ext hl
    refine ⟨l'⁻¹, ?_⟩
    change l'⁻¹ • R₀ = Q
    rw [← hlQ, inv_smul_smul]
  show ((centralizer ({t} : Set G)).subgroupOf N).index = 2 ^ f
  rw [← hstab, MulAction.index_stabilizer, horbit, Set.ncard_univ, Nat.card_coe_set_eq]
  exact hΔ

end U3Start

end CFSG.SeitzReduction.RankOne
