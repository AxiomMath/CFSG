module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiPartitionBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStartInner

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint CFSG.GH74.Uniqueness.Bender

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem torus_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), b ≠ 1 → b' ≠ 1 →
      ∃ x ∈ normalizer (szA₁ (szT₁ L T) : Set G), x * t = t * x ∧ x * b * x⁻¹ = b' := by
  intro b hb b' hb' hb1 hb'1
  obtain ⟨d, -, hdb, hdt, hdT₁, -⟩ := h.exists_cartan_conj_of_card_sylow hS2 hb hb1 hb' hb'1
  have hdA₁ : d ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
    normalizer_le_normalizer_inf_centralizer (szT₁ L T) hdT₁
  refine ⟨d⁻¹, inv_mem hdA₁, (Commute.inv_left hdt).eq, ?_⟩
  rw [inv_inv]
  exact hdb.symm

theorem partitionData_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    SzPartitionData (szA₁ (szT₁ L T)) t :=
  ⟨h.sq_eq_one, centralizer_le (szA₁_le _) h.mem_centralizer_szT₁,
    h.conj_not_mem_szA₁_of_card_sylow hS2,
    fun _ hg => (h.exists_normalizer_conj_of_card_sylow hS2 hg).2,
    h.torus_of_card_sylow hS2, h.exists_conj_eq_mul_ne_one_of_card_sylow hS2⟩

end U3Start

end CFSG.SeitzReduction.RankOne
