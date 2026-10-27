module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Equiv Equiv.Perm

theorem card_centralizer_involution_fin_seven {π : Perm (Fin 7)} (hππ : π * π = 1) (hne : π ≠ 1) :
    (Nat.card (Subgroup.centralizer {π}) = 240 ∧ π.cycleType = {2}) ∨
      Nat.card (Subgroup.centralizer {π}) = 48 := by
  have h2 : π ^ 2 = 1 := by rw [pow_two]; exact hππ
  have hord : orderOf π = 2 := orderOf_eq_prime h2 hne
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := π) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hn
  have hsum : π.cycleType.sum ≤ 7 := by
    simpa using Equiv.Perm.sum_cycleType_le π
  rw [hn, Multiset.sum_replicate] at hsum
  have hn2 : n ≤ 2 := by simp at hsum; omega
  have hcard := Equiv.Perm.nat_card_centralizer π
  rw [hn] at hcard
  interval_cases n
  · left
    refine ⟨?_, by simpa using hn⟩
    rw [hcard]
    decide
  · right
    rw [hcard]
    decide
  · right
    rw [hcard]
    decide

theorem a7_aut_eq_one_of_fixes_large {H₀ : Subgroup (alternatingGroup (Fin 7))}
    (hcard : 120 < Nat.card ↥H₀) {σ : MulAut (alternatingGroup (Fin 7))} (hσ : σ * σ = 1)
    (hfix : ∀ h ∈ H₀, σ h = h) : σ = 1 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  obtain ⟨π, rfl⟩ := hbij.2 σ
  have hππ : π * π = 1 := by
    apply hbij.1
    rw [map_mul, map_one]
    exact hσ
  by_contra hne
  have hπne : π ≠ 1 := fun h => hne (by rw [h, map_one])
  have hle : H₀.map (alternatingGroup (Fin 7)).subtype ≤ Subgroup.centralizer {π} := by
    rintro x ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := congrArg Subtype.val (hfix h hh)
    rw [MulAut.conjNormal_apply] at h1
    have h2 : π * (h : Perm (Fin 7)) = h * π := mul_inv_eq_iff_eq_mul.1 h1
    exact h2.symm
  have hmapcard : Nat.card (H₀.map (alternatingGroup (Fin 7)).subtype) = Nat.card H₀ :=
    Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective
  have hdvd : Nat.card H₀ ∣ Nat.card (Subgroup.centralizer {π}) := by
    rw [← hmapcard]
    exact Subgroup.card_dvd_of_le hle
  rcases card_centralizer_involution_fin_seven hππ hπne with ⟨h240, hct⟩ | h48
  · rw [h240] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hc2 : c < 2 := by
      by_contra h
      have h' : 2 ≤ c := not_lt.1 h
      nlinarith
    have hc1 : Nat.card H₀ = 240 := by
      interval_cases c <;> omega
    have heq : H₀.map (alternatingGroup (Fin 7)).subtype = Subgroup.centralizer {π} :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hmapcard, hc1, h240])
    have hmem : π ∈ H₀.map (alternatingGroup (Fin 7)).subtype := by
      rw [heq]
      exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    obtain ⟨h, -, hh⟩ := hmem
    have hsgn : Perm.sign π = 1 := by
      rw [← Equiv.Perm.mem_alternatingGroup, ← hh]
      exact h.2
    rw [Equiv.Perm.sign_of_cycleType, hct] at hsgn
    revert hsgn
    decide
  · rw [h48] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
