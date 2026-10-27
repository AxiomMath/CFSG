module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRegularModel
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRegularEight
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRegularFour
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRegularBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates

theorem hasRegularNormalSubgroup_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    HasRegularNormalSubgroup (gmsRootConjugateAction (szA L T t) (zpowers t)).range := by
  have h2 := h.two_le
  rcases (show f = 2 ∨ f = 3 ∨ 4 ≤ f by omega) with hf | hf | hf
  · obtain ⟨-, hΔ, htr⟩ := h.partition_of_card_sylow hS2
    refine hasRegularNormalSubgroup_of_card_eq_four ?_ htr
    rw [Nat.card_coe_set_eq, hΔ, hf]
    norm_num
  · exact (h.hasRegularNormalSubgroup_iff_of_card_sylow hS2).mpr
      (h.exists_translation_of_eight_of_card_sylow hS2 hf)
  · rcases h.regularNormal_or_projective_of_card_sylow hS2 (by omega) with hE | ⟨hf3, -⟩
    · exact hE
    · omega

theorem forall_exists_conj_translation_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∀ b ∈ szA₁ (szT₁ L T), ∃ m ∈ normalizer (szA L T t : Set G) ⊓
      centralizer (szA₁ (szT₁ L T) : Set G), m * t * m⁻¹ = b * t := by
  obtain ⟨n, hn, hnt⟩ :=
    h.exists_translation_of_card_sylow hS2 (h.hasRegularNormalSubgroup_of_card_sylow hS2)
  exact h.forall_exists_conj_of_card_sylow hS2 (mem_inf.mp hn).1 (mem_inf.mp hn).2 hnt

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
