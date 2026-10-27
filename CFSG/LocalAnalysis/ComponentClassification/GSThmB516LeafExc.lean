module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafExcTag
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOddJ
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10G2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10F4
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Tri
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Ree
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10TwE6

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.Burgoyne.X10
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open Pump516

theorem Pump516.isSimpleGroup_of_l4u4 {X : Type} [Group X] {p f : ℕ}
    (h : (p ^ f % 4 = 3 ∧ LieModel X .PSL 4 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel X .PSU 4 p f)) :
    IsSimpleGroup X := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact Pump516.isSimpleGroup_of_lieModel_psl (by norm_num) h
  · rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (ClassicalGroups.Unitary.fam_PSU_simplicity X 4 p f h).2
    all_goals exact absurd h0 (by norm_num)

theorem cf516ExcRow_of
    (hA7 : E7TwistedA7P CompPred.model) (h20 : TwE6TwentyP CompPred.model)
    (hA5 : TwE6A5P CompPred.model) : CF516ExcRow := by
  intro S _ _ τ n r e hr hr2 hτ hadm hm hs hna _ σ P hP p f hp hp2 hf hPm t _ ht2 J hJC hJ hJm
    _ _ _ _ _ _
  have hO : LieOrderFormulasInput := CatLeafProof.lieOrderFormulasInput
  have hfam : ExcFamilyModel τ := by
    rcases hτ with hτ | rfl
    · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at hτ
      rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact excFamilyModel_G2_holds
      · exact excFamilyModel_F4_holds
      · exact excFamilyModel_E6_holds
      · exact excFamilyModel_E7_of_A7 hA7
      · exact excFamilyModel_E8_holds
      · exact excFamilyModel_twistedE6_of h20 hA5
      · exact excFamilyModel_trialityD4
    · exact excFamilyModel_twistedG2
  have : IsSimpleGroup S := hs
  have hQ : FixedTwoComponentsQuasisimple S :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna ⟨τ, n, r, e, hr, hr2, hadm, hm⟩
  obtain ⟨hct, hJc, -, hJm'⟩ := leaf_J_data hQ hna ht2 hJC hJ hJm
  have hrp : r = p := by
    rcases hfam S n r e hr hr2 hadm hm _ hct _ hJc with ⟨τ', n', f', -, -, h⟩ | ⟨-, -, hnot, -⟩
    · exact char_eq_of_psl_two_sq hp hp2 hf hr2 hJm' h
    · exact absurd ⟨t, rfl⟩ hnot
  subst hrp
  obtain ⟨hσ2', hPF, hPp, hPtop⟩ := hP
  have hσ1 := ProperFixedComponent.ne_one ⟨hσ2', hPF, hPp, hPtop⟩
  have hσ2 : σ * σ = 1 := MulEquiv.ext fun y => hσ2' y
  have hσo : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  obtain ⟨hPc, -, ⟨eP⟩⟩ := fixed_component_data hQ hσ2 hσ1 hPF hPp (isSimpleGroup_of_l4u4 hPm)
  have hPm' : (r ^ f % 4 = 3 ∧ LieModel (↥(P.subgroupOf (fixedSubgroup σ)) ⧸
        center ↥(P.subgroupOf (fixedSubgroup σ))) .PSL 4 r f) ∨
      (r ^ f % 4 = 1 ∧ LieModel (↥(P.subgroupOf (fixedSubgroup σ)) ⧸
        center ↥(P.subgroupOf (fixedSubgroup σ))) .PSU 4 r f) := by
    rcases hPm with ⟨h3, h⟩ | ⟨h1, h⟩
    · exact Or.inl ⟨h3, lieModel_center_of_fixed eP h⟩
    · exact Or.inr ⟨h1, lieModel_center_of_fixed eP h⟩
  rcases hfam S n r e hr hr2 hadm hm σ hσo _ hPc with ⟨τ', n', f', htag, hadm', h⟩ |
      ⟨-, -, -, h8⟩
  · exact false_of_l4u4_of_excCompTag hO hp2 hf htag hadm' h hPm'
  ·
    have hadm8 : StatedLieAdmissible .PSL 2 2 3 := by
      refine ⟨Nat.prime_two, by norm_num, le_rfl, ?_, ?_⟩ <;> decide
    obtain ⟨-, hord, -⟩ := hO _ .PSL 2 2 3 hadm8 h8
    have h1 : lieOrderDivisor .PSL 2 (2 ^ 3) = 1 := by decide
    have h2 : lieOrderNumerator .PSL 2 (2 ^ 3) = 504 := by decide
    rw [h1, h2, mul_one] at hord
    have hle : Nat.card (↥(P.subgroupOf (fixedSubgroup σ)) ⧸
        center ↥(P.subgroupOf (fixedSubgroup σ))) ≤ 504 :=
      hord ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have hlow := pow_fifteen_le_four_mul_card hp hp2 hf hPm'
    have hq3 : 3 ^ 15 ≤ (r ^ f) ^ 15 :=
      Nat.pow_le_pow_left (le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) r))
        15
    omega

end CFSG.ComponentClassification.GSThmB
