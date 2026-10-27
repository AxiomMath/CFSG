module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.SubgroupIndicatorElementaryPlane
import CFSG.FeitThompson.Foundations.AbelianSolvable
import CFSG.FeitThompson.Local.WielandtFixedPointOrderSolvable
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {p : ℕ} {A K : Type*} [Group A] [Group K]

theorem fixedPoints_comp_subtype_bot (ρ : A →* MulAut K) :
    FixedPoints.subgroup (ρ.comp (⊥ : Subgroup A).subtype).range K = ⊤ := by
  ext v
  simp only [mem_fixedPoints_comp_subtype_iff, Subgroup.mem_bot, Subgroup.mem_top, iff_true]
  intro b hb
  subst hb
  simp

theorem fixedPoints_comp_subtype_top (ρ : A →* MulAut K) :
    FixedPoints.subgroup (ρ.comp (⊤ : Subgroup A).subtype).range K
      = FixedPoints.subgroup ρ.range K := by
  ext v
  rw [mem_fixedPoints_comp_subtype_iff, mem_fixedPoints_range_iff ρ]
  exact ⟨fun h a => h a (Subgroup.mem_top a), fun h b _ => h b⟩

theorem natCard_mul_natCard_fixedPoints_pow_eq_finprod (hp : p.Prime) (hcard : Nat.card A = p ^ 2)
    (hexp : ∀ a : A, a ^ p = 1) [Finite K] [Group.IsSolvable K] (ρ : A →* MulAut K)
    (hpK : ¬ p ∣ Nat.card K) :
    Nat.card K * Nat.card (FixedPoints.subgroup ρ.range K) ^ p
      = ∏ᶠ B ∈ subgroupsOfCard A p,
          Nat.card (FixedPoints.subgroup (ρ.comp B.subtype).range K) := by
  classical
  have hA : Finite A := Nat.finite_of_card_ne_zero (by simp [hcard, hp.ne_zero])
  have hAft : Fintype (Subgroup A) := Fintype.ofFinite _
  have hfact : Fact p.Prime := ⟨hp⟩
  have hcomm : IsMulCommutative A := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hcard
  have hsolvA : Group.IsSolvable A := isSolvable_of_isMulCommutative
  have hcop : (Nat.card A).Coprime (Nat.card K) := by
    rw [hcard]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK)
  have hLfin : (subgroupsOfCard A p).Finite := finite_subgroupsOfCard p
  set C : Subgroup A → ℕ :=
    fun B => Nat.card (FixedPoints.subgroup (ρ.comp B.subtype).range K) with hC
  have hCtop : C ⊤ = Nat.card (FixedPoints.subgroup ρ.range K) := by
    rw [hC]; simp only [fixedPoints_comp_subtype_top]
  have hCbot : C ⊥ = Nat.card K := by
    rw [hC]; simp only [fixedPoints_comp_subtype_bot, Subgroup.card_top]
  set m : Subgroup A → ℕ :=
    fun B => (if B = ⊤ then 1 else 0) + (if B = ⊥ then p else 0) with hm
  set n : Subgroup A → ℕ := fun B => if B ∈ subgroupsOfCard A p then 1 else 0 with hn
  have hmn : ∀ a : A, ∑ B with a ∈ B, m B = ∑ B with a ∈ B, n B := by
    intro a
    have hid := indicator_identity_of_card_eq_sq hp hcard hexp a
    rw [finsum_mem_eq_finite_toFinset_sum _ hLfin] at hid
    have hind : ∀ B : Subgroup A, ((B : Set A)).indicator (1 : A → ℕ) a
        = if a ∈ B then 1 else 0 := fun B => by simp [Set.indicator_apply]
    simp only [hind] at hid
    rw [Finset.sum_filter, Finset.sum_filter]
    have hR : ∑ B : Subgroup A, (if a ∈ B then n B else 0)
        = ∑ B ∈ hLfin.toFinset, (if a ∈ B then 1 else 0) := by
      rw [Finset.sum_congr rfl (g := fun B => if B ∈ hLfin.toFinset
          then (if a ∈ B then 1 else 0) else 0) (fun B _ => by
            simp only [hn, hLfin.mem_toFinset]
            split <;> simp), ← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter]
    have hL1 : ∑ B : Subgroup A, (if a ∈ B then (if B = ⊤ then 1 else 0) else 0)
        = if a ∈ (⊤ : Subgroup A) then 1 else 0 := by
      rw [Finset.sum_congr rfl (g := fun B : Subgroup A => if B = ⊤
        then (if a ∈ (⊤ : Subgroup A) then 1 else 0) else 0) (fun B _ => by
          by_cases hB : a ∈ B
          · simp [hB]
          · rw [if_neg hB, if_neg (fun h : B = ⊤ => hB (h ▸ Subgroup.mem_top a))]),
        Finset.sum_ite_eq']
      simp
    have hL2 : ∑ B : Subgroup A, (if a ∈ B then (if B = ⊥ then p else 0) else 0)
        = if a ∈ (⊥ : Subgroup A) then p else 0 := by
      rw [Finset.sum_congr rfl (g := fun B : Subgroup A => if B = ⊥
        then (if a ∈ (⊥ : Subgroup A) then p else 0) else 0) (fun B _ => by
          by_cases hB : B = ⊥
          · subst hB; simp
          · simp [hB]), Finset.sum_ite_eq']
      simp
    have hLsplit : ∑ B : Subgroup A, (if a ∈ B then m B else 0)
        = (∑ B : Subgroup A, (if a ∈ B then (if B = ⊤ then 1 else 0) else 0))
          + ∑ B : Subgroup A, (if a ∈ B then (if B = ⊥ then p else 0) else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun B _ => by simp only [hm]; split <;> simp
    rw [hLsplit, hL1, hL2, hR, ← hid, mul_ite, mul_one, mul_zero]
    ring
  have key := prod_natCard_fixedPoints_comp_subtype_pow_eq ρ hcop id m n hmn
  simp only [id_eq] at key
  have hne : (⊤ : Subgroup A) ≠ (⊥ : Subgroup A) := by
    intro h
    have h1 : Nat.card A = 1 := by
      rw [← Subgroup.card_top (G := A), h, Subgroup.card_bot]
    rw [hcard] at h1
    exact absurd h1 (Nat.one_lt_pow two_ne_zero hp.one_lt).ne'
  have hLHS : ∏ B : Subgroup A, C B ^ (m B * Nat.card B) = C ⊤ ^ (p ^ 2) * C ⊥ ^ p := by
    rw [Finset.prod_eq_mul_of_mem ⊤ ⊥ (Finset.mem_univ _) (Finset.mem_univ _) hne ?_]
    · simp only [hm, if_pos, if_neg hne, if_neg hne.symm]
      simp [hcard]
    · intro B _ hB
      simp only [hm, if_neg hB.1, if_neg hB.2]
      simp
  have hRHS : ∏ B : Subgroup A, C B ^ (n B * Nat.card B) = ∏ B ∈ hLfin.toFinset, C B ^ p := by
    rw [Finset.prod_congr rfl (g := fun B : Subgroup A =>
      if B ∈ hLfin.toFinset then C B ^ p else 1) (fun B _ => by
        simp only [hn]
        by_cases hB : B ∈ subgroupsOfCard A p
        · rw [if_pos hB, if_pos (hLfin.mem_toFinset.2 hB), one_mul,
            mem_subgroupsOfCard.mp hB]
        · rw [if_neg hB, if_neg (fun h => hB (hLfin.mem_toFinset.1 h)), zero_mul, pow_zero]),
      ← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hLHS, hRHS, hCtop, hCbot] at key
  rw [finprod_mem_eq_finite_toFinset_prod _ hLfin]
  refine Nat.pow_left_injective hp.ne_zero ?_
  simp only [← hC]
  rw [mul_pow, ← pow_mul, ← Finset.prod_pow, ← sq, ← key]
  ring

theorem natCard_mul_natCard_centralizer_pow_eq_finprod (hp : p.Prime) (hcard : Nat.card A = p ^ 2)
    (hexp : ∀ a : A, a ^ p = 1) [Finite K] [Group.IsSolvable K] (ρ : A →* MulAut K)
    (hpK : ¬ p ∣ Nat.card K) :
    Nat.card K * Nat.card {x : K // ∀ a : A, ρ a x = x} ^ p
      = ∏ᶠ B ∈ subgroupsOfCard A p, Nat.card {x : K // ∀ b ∈ B, ρ b x = x} := by
  have h1 : Nat.card {x : K // ∀ a : A, ρ a x = x} = Nat.card (FixedPoints.subgroup ρ.range K) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => (mem_fixedPoints_range_iff ρ).symm)
  have h2 : ∀ B : Subgroup A, Nat.card {x : K // ∀ b ∈ B, ρ b x = x}
      = Nat.card (FixedPoints.subgroup (ρ.comp B.subtype).range K) := fun B =>
    (natCard_fixedPoints_comp_subtype_eq_natCard_subtype ρ B).symm
  rw [h1]
  simp only [h2]
  exact natCard_mul_natCard_fixedPoints_pow_eq_finprod hp hcard hexp ρ hpK

theorem natCard_mul_natCard_fixedPoints_pow_eq_finprod_of_mulEquiv
    (e : A ≃* Multiplicative (ZMod p × ZMod p)) (hp : p.Prime) [Finite K] [Group.IsSolvable K]
    (ρ : A →* MulAut K) (hpK : ¬ p ∣ Nat.card K) :
    Nat.card K * Nat.card (FixedPoints.subgroup ρ.range K) ^ p
      = ∏ᶠ B ∈ subgroupsOfCard A p,
          Nat.card (FixedPoints.subgroup (ρ.comp B.subtype).range K) :=
  natCard_mul_natCard_fixedPoints_pow_eq_finprod hp (card_eq_sq_of_mulEquiv e hp)
    (pow_eq_one_of_mulEquiv e hp) ρ hpK

end CFSG.FeitThompson
