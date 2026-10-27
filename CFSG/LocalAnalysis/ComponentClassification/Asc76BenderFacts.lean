module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XInputs
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsCover

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ComponentClassification.Asc76

section SzOrU3

variable {L : Type*} [Group L]

theorem exists_fusionBenderBorel_of_isSzOrU3 [Finite L] (hL : IsSzOrU3 L) :
    ∃ q k : ℕ, 2 ≤ q ∧ fusionBenderBorel L q k := by
  rcases hL with ⟨a, ha, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
  · refine ⟨2 ^ (2 * a + 1), 2, ?_, fusionBenderBorel_of_mulEquiv_sz ha e⟩
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 1 ≤ 2 * a + 1 by omega))
  · refine ⟨2 ^ f, 3, ?_, fusionBenderBorel_of_mulEquiv_psu3 hf e⟩
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 1 ≤ f by omega))

theorem isBenderGroup_of_isSzOrU3 (hL : IsSzOrU3 L) : CFSG.BenderSuzuki.IsBenderGroup L := by
  rcases hL with ⟨a, ha, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
  · exact isBenderGroup_of_mulEquiv_sz ha e
  · exact isBenderGroup_of_mulEquiv_psu3 hf e

theorem card_sylow_of_isSzOrU3 [Finite L] (hL : IsSzOrU3 L) (P : Sylow 2 L) :
    Nat.card (Sylow 2 L) = Nat.card (P : Subgroup L) + 1 := by
  rcases hL with ⟨a, ha, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
  · exact card_sylow_of_mulEquiv_sz ha e P
  · exact card_sylow_of_mulEquiv_psu3 hf e P

end SzOrU3

theorem benderFacts : BenderFacts where
  sylow_inf L _ _ hL _ _ hne := by
    obtain ⟨q, k, -, hB⟩ := exists_fusionBenderBorel_of_isSzOrU3 hL
    exact inf_eq_bot_of_fusionBenderBorel hB hne
  sylow_transitive L _ _ hL P _ _ h₀ hS := by
    obtain ⟨q, k, -, hB⟩ := exists_fusionBenderBorel_of_isSzOrU3 hL
    exact exists_mem_smul_eq_of_fusionBenderBorel hB (card_sylow_of_isSzOrU3 hL P) h₀ hS
  aut_fix_sylow L _ _ hL P φ hφ :=
    exists_eq_conj_of_forall_apply_eq (isBenderGroup_of_isSzOrU3 hL) P φ hφ
  center_sq L _ _ hL P _ hcP hc := by
    obtain ⟨q, k, -, hB⟩ := exists_fusionBenderBorel_of_isSzOrU3 hL
    exact sq_eq_one_of_fusionBenderBorel hB P hcP hc
  involution_center L _ _ hL P _ hxP hx := by
    obtain ⟨q, k, hq, hB⟩ := exists_fusionBenderBorel_of_isSzOrU3 hL
    exact mem_centralizer_of_fusionBenderBorel hB hq P hxP hx
  aut_involution_center L _ _ hL P φ hφ2 hφP _ hzP hz := by
    rcases hL with ⟨a, ha, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
    · exact apply_eq_of_mulEquiv_sz ha e P φ hφ2 hφP hz
    · exact apply_eq_of_mulEquiv_psu3 hf e P φ hφ2 hφP hzP hz
  cover Y _ _ Z _ hZc hZ2 hY := by
    by_cases hle : Z ≤ commutator Y
    · right
      rcases hY with ⟨a, ha, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
      · obtain rfl := eq_one_of_le_commutator_of_mulEquiv_sz hZc hZ2 ha e hle
        exact ⟨e⟩
      · exact absurd hle (not_le_commutator_of_mulEquiv_psu3 hZc hZ2 hf e)
    · exact Or.inl hle

end CFSG.ComponentClassification.Asc76X
