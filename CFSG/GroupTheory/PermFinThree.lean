module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LieType.BorelTits.Basic
import CFSG.ClassicalInvolution.Asc77.AscMuTabGroup
import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport

public section

open scoped commutatorElement

namespace CFSG.GroupTheory

private theorem card_alternatingGroup_fin_three : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem pCore_two_perm_fin_three : CFSG.pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.Semidihedral.Local.normal_isPGroup_two_eq_bot
    (MulEquiv.refl (Equiv.Perm (Fin 3))) (CFSG.pCore 2 (Equiv.Perm (Fin 3)))
    pCore_normal (CFSG.pCore_isPGroup (p := 2) (G := Equiv.Perm (Fin 3)))

private theorem isPGroup_alternatingGroup_fin_three :
    IsPGroup 3 (alternatingGroup (Fin 3)) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [card_alternatingGroup_fin_three]
  norm_num

theorem pCore_three_perm_fin_three : CFSG.pCore 3 (Equiv.Perm (Fin 3)) =
    alternatingGroup (Fin 3) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A : Subgroup (Equiv.Perm (Fin 3)) := alternatingGroup (Fin 3) with hA
  have hAle : A ≤ CFSG.pCore 3 (Equiv.Perm (Fin 3)) :=
    CFSG.LieType.BorelTits.le_pCore 3 (inferInstance : A.Normal) isPGroup_alternatingGroup_fin_three
  have hcardA : Nat.card A = 3 := card_alternatingGroup_fin_three
  have hcardNle : Nat.card (CFSG.pCore 3 (Equiv.Perm (Fin 3))) ≤ 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (CFSG.pCore_isPGroup (p := 3) (G := Equiv.Perm (Fin 3)))
    have hdvd : Nat.card (CFSG.pCore 3 (Equiv.Perm (Fin 3))) ∣ 6 := by
      rw [← CFSG.ClassicalInvolution.Asc77.MuTab.card_perm3]
      exact Subgroup.card_subgroup_dvd_card _
    have hk1 : k ≤ 1 := by
      by_contra h
      have hk2 : 2 ≤ k := by omega
      have h9 : 9 ∣ 3 ^ k := dvd_trans (by norm_num : 9 ∣ 3 ^ 2) (pow_dvd_pow 3 hk2)
      rw [← hk] at h9
      have h96 : 9 ∣ 6 := h9.trans hdvd
      omega
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hAle (by rw [hcardA]; exact hcardNle)).symm

theorem card_eq_two_of_isPGroup_two_of_ne_bot {B : Subgroup (Equiv.Perm (Fin 3))}
    (hB : IsPGroup 2 B) (hne : B ≠ ⊥) : Nat.card B = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB
  have hdvd : Nat.card B ∣ 6 := by
    rw [← CFSG.ClassicalInvolution.Asc77.MuTab.card_perm3]
    exact Subgroup.card_subgroup_dvd_card B
  have hk1 : k ≤ 1 := by
    by_contra h
    have hk2 : 2 ≤ k := by omega
    have h4 : 4 ∣ 2 ^ k := dvd_trans (by norm_num : 4 ∣ 2 ^ 2) (pow_dvd_pow 2 hk2)
    rw [← hk] at h4
    have h46 : 4 ∣ 6 := h4.trans hdvd
    omega
  have hk0 : k ≠ 0 := by
    intro hk0
    apply hne
    exact Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero])
  have hk_eq : k = 1 := by omega
  rw [hk, hk_eq]
  norm_num

theorem commutator_alternatingGroup_fin_three_of_card_eq_two
    {B : Subgroup (Equiv.Perm (Fin 3))} (hB : Nat.card B = 2) :
    ⁅alternatingGroup (Fin 3), B⁆ = alternatingGroup (Fin 3) := by
  classical
  set A : Subgroup (Equiv.Perm (Fin 3)) := alternatingGroup (Fin 3) with hA
  have hle : ⁅A, B⁆ ≤ A := Subgroup.commutator_le_left A B
  have hBnt : Nontrivial B := Finite.one_lt_card_iff_nontrivial.1 (by rw [hB]; norm_num)
  obtain ⟨b, hbne⟩ := exists_ne (1 : B)
  have hb : (b : Equiv.Perm (Fin 3)) ∈ B := b.2
  have hb1 : (b : Equiv.Perm (Fin 3)) ≠ 1 := fun h => hbne (Subtype.ext h)
  have hb2 : (b : Equiv.Perm (Fin 3)) * (b : Equiv.Perm (Fin 3)) = 1 := by
    have h := pow_card_eq_one' (x := b)
    rw [hB] at h
    simpa [pow_two] using congrArg Subtype.val h
  set c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2 with hc
  have hcA : c ∈ A := by
    rw [hA, Equiv.Perm.mem_alternatingGroup]
    decide
  have hcne : ⁅c, (b : Equiv.Perm (Fin 3))⁆ ≠ 1 := by
    have h : ∀ y : Equiv.Perm (Fin 3), y * y = 1 → y ≠ 1 → ⁅c, y⁆ ≠ 1 := by
      decide
    exact h _ hb2 hb1
  have hne : ⁅A, B⁆ ≠ ⊥ := by
    intro hbot
    have hmem : ⁅c, (b : Equiv.Perm (Fin 3))⁆ ∈ ⁅A, B⁆ :=
      Subgroup.commutator_mem_commutator hcA hb
    rw [hbot] at hmem
    exact hcne (Subgroup.mem_bot.mp hmem)
  have hdvd : Nat.card ↥(⁅A, B⁆) ∣ 3 := by
    have h1 : Nat.card ((⁅A, B⁆).subgroupOf A) ∣ Nat.card ↥A :=
      Subgroup.card_subgroup_dvd_card _
    rw [card_alternatingGroup_fin_three] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  have hcard : Nat.card ↥(⁅A, B⁆) = 3 := by
    have hne1 : Nat.card ↥(⁅A, B⁆) ≠ 1 := fun h1 => hne (Subgroup.card_eq_one.mp h1)
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
    · exact absurd h1 hne1
    · exact h3
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_alternatingGroup_fin_three])

end CFSG.GroupTheory
