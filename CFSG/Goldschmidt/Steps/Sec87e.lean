module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec85a
import CFSG.Goldschmidt.Steps.Sec85c
import CFSG.Goldschmidt.Steps.Sec87c
import CFSG.Goldschmidt.Steps.Sec87d
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem commutator_sylow_ne_bot (hS : ¬ IsMulCommutative (S : Subgroup G)) :
    ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≠ ⊥ := by
  intro hS'
  refine hS ⟨⟨fun u v => Subtype.ext ?_⟩⟩
  have h := Subgroup.commutator_mem_commutator u.2 v.2
  rw [hS', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem le_commutator (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hS : ¬ IsMulCommutative (S : Subgroup G))
    (hΩ : A = Omega1 ((S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G))) :
    A ≤ ⁅(S : Subgroup G), (S : Subgroup G)⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := ⁅(S : Subgroup G), (S : Subgroup G)⁆ with hD
  have hDS : D ≤ S := commutator_self_le _
  have hSD : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := fun s hs =>
    mem_normalizer_commutator (Subgroup.le_normalizer hs)
  have hne := inf_center_ne_bot' S.isPGroup' hDS hSD (commutator_sylow_ne_bot hS)
  obtain ⟨w, ⟨hwD, hwZ⟩, hw1, hw2⟩ :=
    exists_involution (S.isPGroup'.to_le (inf_le_left.trans hDS)) hne
  have hwA : w ∈ A := by
    rw [hΩ]
    exact Subgroup.subset_closure ⟨hwZ, hw2⟩
  obtain ⟨x, hxS, hxwA, hxw⟩ := exists_mem_normalizer_sylow hset h4 hwA hw1
  have hxwD : x⁻¹ * w * x ∈ D := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_commutator (Subgroup.inv_mem _ hxS)) w).mp hwD
  intro c hc
  rcases mem_four hset.elem h4 hwA hxwA hc hw1 (by simpa using conj_ne_one (n := x⁻¹) hw1)
    (Ne.symm hxw) with h | h | h | h
  · exact h ▸ D.one_mem
  · exact h ▸ hwD
  · exact h ▸ hxwD
  · exact h ▸ D.mul_mem hwD hxwD

theorem eq_omega1_commutator (hset : GoldSetting G S A)
    (hAD : A ≤ ⁅(S : Subgroup G), (S : Subgroup G)⁆)
    (hC2 : ∀ u ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆, u ^ 2 = 1 → u ∈ A) :
    A = Omega1 ⁅(S : Subgroup G), (S : Subgroup G)⁆ := by
  refine le_antisymm (fun c hc => ?_) ((Subgroup.closure_le _).mpr fun u hu => hC2 u hu.1 hu.2)
  show c ∈ Subgroup.closure _
  exact Subgroup.subset_closure ⟨hAD hc, hset.elem.2 c hc⟩

end CFSG.Goldschmidt.Sec8
