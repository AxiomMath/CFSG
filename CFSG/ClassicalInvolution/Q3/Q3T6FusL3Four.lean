module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn
public import CFSG.ClassicalInvolution.AschTight.S19TBr3
public import Certificates.Data.ExceptionalSL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices (slQuatI)
open scoped MatrixGroups

section Four

theorem Aut.eq_one_or_neg_one_of_sq_eq_one :
    ∀ g : SL(2, ZMod 3), g * g = 1 → g = 1 ∨ g = -1 := by
  decide +kernel

theorem exists_fixed_of_mem_inn3 {β : MulAut SL(2, ZMod 3)} (hβ : β * β = 1) (hi : β ∈ inn3) :
    ∃ h : SL(2, ZMod 3), orderOf h = 4 ∧ β h = h := by
  obtain ⟨g, rfl⟩ := mem_inn3_iff.mp hi
  have hF : ringChar (ZMod 3) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    norm_num
  have hcen : g * g ∈ Subgroup.center SL(2, ZMod 3) := by
    rw [← Aut.ker_conj_sl2Three, MonoidHom.mem_ker, map_mul]
    exact hβ
  rcases (Aut.mem_center_sl2Three_iff _).mp hcen with h1 | h1
  ·
    have hg : (MulAut.conj g : MulAut SL(2, ZMod 3)) = 1 := by
      rcases Aut.eq_one_or_neg_one_of_sq_eq_one g h1 with rfl | rfl
      · exact map_one _
      · rw [← MonoidHom.mem_ker, Aut.ker_conj_sl2Three, Aut.mem_center_sl2Three_iff]
        right
        rfl
    refine ⟨slQuatI (ZMod 3), S19T.orderOf_slQuatI hF, ?_⟩
    rw [hg]
    rfl
  ·
    refine ⟨g, ?_, ?_⟩
    · have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g) ?_ ?_
      · simpa using h
      · intro h2
        rw [pow_one, sq, h1] at h2
        revert h2
        decide +kernel
      · have h4 : g ^ (2 ^ (1 + 1)) = (g * g) * (g * g) := by
          rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, sq]
        rw [h4, h1]
        decide +kernel
    · rw [MulAut.conj_apply]
      group

end Four

section Four3

variable {G : Type} [Group G] [Finite G]

theorem exists_orderOf_four_of_four_group3 (J : Subgroup G)
    (e₁ : ↥J ⧸ classicalInvolutionOddCore ↥J ≃* SL(2, ZMod 3))
    (a b : Subgroup.normalizer (J : Set G)) (ha2 : (a : G) * a = 1) (hb2 : (b : G) * b = 1)
    (hab : (a : G) * b = b * a) (hna : ¬ ∃ w ∈ J, orderOf w = 4 ∧ w * a = a * w) :
    (∃ w ∈ J, orderOf w = 4 ∧ w * b = b * w) ∨
      ∃ w ∈ J, orderOf w = 4 ∧ w * ((a : G) * b) = ((a : G) * b) * w := by
  have hinv : ∀ n : Subgroup.normalizer (J : Set G), (n : G) * n = 1 →
      S19T.oddAct J e₁ n * S19T.oddAct J e₁ n = 1 := by
    intro n hn
    rw [← map_mul, show n * n = 1 from Subtype.ext hn, map_one]
  have h2grp : ∀ n : Subgroup.normalizer (J : Set G), (n : G) * n = 1 →
      IsPGroup 2 (Subgroup.zpowers (n : G)) := fun n hn =>
    (S19Q.isPGroup_zpowers_iff_exists_pow (n : G)).mpr ⟨1, by rw [pow_one, sq, hn]⟩
  have hlift : ∀ n : Subgroup.normalizer (J : Set G), (n : G) * n = 1 →
      S19T.oddAct J e₁ n ∈ inn3 → ∃ w ∈ J, orderOf w = 4 ∧ w * n = n * w := by
    intro n hn hni
    obtain ⟨h, hh, hfix⟩ := exists_fixed_of_mem_inn3 (hinv n hn) hni
    exact S19T.exists_orderOf_four_of_fixed J e₁ n (h2grp n hn) hh hfix
  have hαi : S19T.oddAct J e₁ a ∉ inn3 := fun h => hna (by
    obtain ⟨w, hw, hw4, hwa⟩ := hlift a ha2 h
    exact ⟨w, hw, hw4, hwa⟩)
  by_cases hβi : S19T.oddAct J e₁ b ∈ inn3
  · left
    obtain ⟨w, hw, hw4, hwb⟩ := hlift b hb2 hβi
    exact ⟨w, hw, hw4, hwb⟩
  right
  have hab2 : ((a * b : Subgroup.normalizer (J : Set G)) : G) * (a * b) = 1 := by
    rw [Subgroup.coe_mul]
    calc (a : G) * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = 1 := by rw [← mul_assoc, ha2, one_mul, hb2]
  have hαβi : S19T.oddAct J e₁ (a * b) ∈ inn3 := by
    rw [map_mul, Subgroup.mul_mem_iff_of_index_two inn3_index]
    exact ⟨fun h => absurd h hαi, fun h => absurd h hβi⟩
  obtain ⟨w, hw, hw4, hwc⟩ := hlift (a * b) hab2 hαβi
  exact ⟨w, hw, hw4, by rw [← Subgroup.coe_mul]; exact hwc⟩

end Four3

end CFSG.ClassicalInvolution.Q3.Q3T6
