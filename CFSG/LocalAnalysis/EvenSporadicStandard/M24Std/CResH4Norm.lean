module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResTLat
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH4Count
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH4

open Subgroup Equiv Equiv.Perm

theorem perm6_normal_bot_or_alt (N : Subgroup (Perm (Fin 6))) (hN : N.Normal) :
    N = ⊥ ∨ alternatingGroup (Fin 6) ≤ N := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have : (N.subgroupOf (alternatingGroup (Fin 6))).Normal := hN.subgroupOf _
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 6))) with
    hbot | htop
  · left
    rw [eq_bot_iff]
    intro b hb
    rw [mem_bot]
    apply centralizer_alt_six
    intro a _
    have hmemN : a * b * a⁻¹ * b⁻¹ ∈ N := mul_mem (hN.conj_mem b hb a) (inv_mem hb)
    have hmemA : a * b * a⁻¹ * b⁻¹ ∈ alternatingGroup (Fin 6) := by
      rw [mem_alternatingGroup]
      simp only [map_mul, map_inv]
      rw [mul_inv_cancel_comm, mul_inv_cancel]
    have hmem : (⟨_, hmemA⟩ : alternatingGroup (Fin 6)) ∈
        N.subgroupOf (alternatingGroup (Fin 6)) := mem_subgroupOf.2 hmemN
    rw [hbot, mem_bot] at hmem
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := congrArg Subtype.val hmem
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm
  · exact Or.inr (subgroupOf_eq_top.1 htop)

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem card_perm_six : Nat.card (Perm (Fin 6)) = 720 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem card_ker_snd :
    Nat.card (MonoidHom.snd (Multiplicative (ZMod 2)) (Perm (Fin 6))).ker = 2 := by
  have h := Subgroup.card_ker_mul_card_range
    (MonoidHom.snd (Multiplicative (ZMod 2)) (Perm (Fin 6)))
  rw [MonoidHom.range_eq_top_of_surjective _ (fun y => ⟨(1, y), rfl⟩), card_top, Nat.card_prod,
    card_perm_six] at h
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 2
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem arith_cases (b d m : ℕ) (h360 : 360 ∣ b) (h720 : b ∣ 720) (hd : d = 1 ∨ d = 2)
    (hm : b * d = m) : m = 360 ∨ m = 720 ∨ m = 1440 := by
  obtain ⟨k, hk⟩ := h360
  have hle : b ≤ 720 := Nat.le_of_dvd (by norm_num) h720
  have hpos : 0 < b := Nat.pos_of_dvd_of_pos h720 (by norm_num)
  subst hk
  have hk2 : k = 1 ∨ k = 2 := by omega
  rcases hk2 with rfl | rfl <;> rcases hd with rfl | rfl <;> omega

theorem normal_z2s6_cases (M : Subgroup (Multiplicative (ZMod 2) × Perm (Fin 6))) (hM : M.Normal) :
    (Nat.card M = 1 ∨ Nat.card M = 2) ∨
      (alternatingGroup (Fin 6) ≤ M.map (MonoidHom.snd (Multiplicative (ZMod 2)) (Perm (Fin 6))) ∧
        (Nat.card M = 360 ∨ Nat.card M = 720 ∨ Nat.card M = 1440)) := by
  have hsurj : Function.Surjective (MonoidHom.snd (Multiplicative (ZMod 2)) (Perm (Fin 6))) :=
    fun y => ⟨(1, y), rfl⟩
  have hc := natCard_map_mul_natCard_inf_ker
    (MonoidHom.snd (Multiplicative (ZMod 2)) (Perm (Fin 6))) M
  have hd : Nat.card ↥(M ⊓ (MonoidHom.snd (Multiplicative (ZMod 2)) (Perm (Fin 6))).ker) ∣ 2 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : M ⊓
      (MonoidHom.snd (Multiplicative (ZMod 2)) (Perm (Fin 6))).ker ≤ _)
    rwa [card_ker_snd] at this
  have hd' : Nat.card ↥(M ⊓ (MonoidHom.snd (Multiplicative (ZMod 2)) (Perm (Fin 6))).ker) = 1 ∨
      Nat.card ↥(M ⊓ (MonoidHom.snd (Multiplicative (ZMod 2)) (Perm (Fin 6))).ker) = 2 :=
    (Nat.dvd_prime Nat.prime_two).1 hd
  rcases perm6_normal_bot_or_alt _ (hM.map _ hsurj) with hbot | hA
  · left
    rw [hbot, Subgroup.card_bot, one_mul] at hc
    rw [← hc]
    exact hd'
  · right
    refine ⟨hA, ?_⟩
    have h360 : 360 ∣ Nat.card
        (M.map (MonoidHom.snd (Multiplicative (ZMod 2)) (Perm (Fin 6)))) := by
      rw [← card_alternatingGroup_six]
      exact Subgroup.card_dvd_of_le hA
    have h720 : Nat.card
        (M.map (MonoidHom.snd (Multiplicative (ZMod 2)) (Perm (Fin 6)))) ∣ 720 := by
      rw [← card_perm_six]
      exact Subgroup.card_subgroup_dvd_card _
    exact arith_cases _ _ _ h360 h720 hd' hc

theorem card_normal_z2s6 (M : Subgroup (Multiplicative (ZMod 2) × Perm (Fin 6))) (hM : M.Normal) :
    Nat.card M = 1 ∨ Nat.card M = 2 ∨ Nat.card M = 360 ∨ Nat.card M = 720 ∨
      Nat.card M = 1440 := by
  rcases normal_z2s6_cases M hM with h | ⟨-, h⟩
  · rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem normal_z2s6_eq_bot_of_odd (M : Subgroup (Multiplicative (ZMod 2) × Perm (Fin 6)))
    (hM : M.Normal) (hodd : Odd (Nat.card M)) : M = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  rcases card_normal_z2s6 M hM with h | h | h | h | h
  · exact h
  all_goals
    exfalso
    rw [h] at hodd
    revert hodd
    decide

theorem snd_eq_one_of_commute_normal (M : Subgroup (Multiplicative (ZMod 2) × Perm (Fin 6)))
    (hM : M.Normal) (h360 : Nat.card M = 360)
    (q : Multiplicative (ZMod 2) × Perm (Fin 6)) (hq : ∀ m ∈ M, q * m = m * q) : q.2 = 1 := by
  rcases normal_z2s6_cases M hM with h | ⟨hA, -⟩
  · exfalso
    rcases h with h | h <;> exact absurd (h360.symm.trans h) (by norm_num)
  · apply centralizer_alt_six
    intro a ha
    obtain ⟨m, hmM, hma⟩ := hA ha
    have h := congrArg Prod.snd (hq m hmM)
    simp only [Prod.snd_mul] at h
    rw [← hma]
    exact h

end CFSG.EvenSporadicStandard.M24Std.CResH4
