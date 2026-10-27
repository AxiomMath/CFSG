module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.SolvableGroupElemAbelianMinNormal
import CFSG.FeitThompson.Foundations.CoprimeAbelianNormalComplements
import CFSG.FeitThompson.Foundations.LiftHallByNormalComplement
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
import CFSG.FeitThompson.Foundations.HallLiftThroughNormalPi

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

universe u

theorem isMulCommutative_of_mulEquiv {A B : Type*} [Mul A] [Mul B] [IsMulCommutative B]
    (e : A ≃* B) : IsMulCommutative A :=
  IsMulCommutative.of_comm fun a b => e.injective (by rw [map_mul, map_mul, mul_comm' (e a) (e b)])

theorem isPiNumber_pow_of_prime {π : Set ℕ} {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d) (hpπ : p ∈ π) :
    IsPiNumber π (p ^ d) :=
  isPiNumber_iff.2 fun q hq => by
    rw [Nat.primeFactors_pow _ (by omega), hp.primeFactors, Finset.mem_singleton] at hq
    exact hq ▸ hpπ

private theorem exists_isHallSubgroup_aux (π : Set ℕ) (n : ℕ) :
    ∀ (X : Type u) [Group X] [Finite X] [Group.IsSolvable X],
      Nat.card X ≤ n → ∃ H : Subgroup X, IsHallSubgroup π H := by
  induction n with
  | zero =>
    intro X _ _ _ h
    exact absurd h (by have := Nat.card_pos (α := X); omega)
  | succ n ih =>
    intro X _ _ _ hcard
    rcases eq_or_ne (Nat.card X) 1 with h1 | h1
    · exact ⟨⊤, isHallSubgroup_top_iff.2 (by rw [h1]; exact isPiNumber_one)⟩
    have : Nontrivial X :=
      Finite.one_lt_card_iff_nontrivial.1 (by have := Nat.card_pos (α := X); omega)
    obtain ⟨N, hNmin, p, d, hp, hd, ⟨e⟩⟩ :=
      exists_minimal_normal_ne_bot_nonempty_mulEquiv (G := X)
    obtain ⟨hNnormal, hNbot, -⟩ := minimal_normal_ne_bot_iff.1 hNmin
    have := hNnormal
    have hNcomm : IsMulCommutative ↥N := isMulCommutative_of_mulEquiv e
    have hNcard : Nat.card ↥N = p ^ d := by
      have : Fact p.Prime := ⟨hp⟩
      rw [Nat.card_eq_of_bijective e e.bijective]
      simp [Nat.card_eq_fintype_card]
    have hlt : Nat.card (X ⧸ N) < Nat.card X :=
      natCard_quotient_lt_natCard_of_bot_lt N (bot_lt_iff_ne_bot.2 hNbot)
    obtain ⟨J, hJ⟩ := ih (X ⧸ N) (by omega)
    by_cases hpπ : p ∈ π
    ·
      exact ⟨J.comap (QuotientGroup.mk' N),
        IsHallSubgroup.comap_mk' (hNcard ▸ isPiNumber_pow_of_prime hp hd hpπ) hJ⟩
    ·
      have hNpi' : IsPiNumber πᶜ (Nat.card ↥N) := hNcard ▸ isPiNumber_pow_of_prime hp hd hpπ
      set K := J.comap (QuotientGroup.mk' N) with hK
      have hNK : N ≤ K := le_comap_mk' J
      set A := N.subgroupOf K with hA
      have : A.Normal := hNnormal.subgroupOf K
      have eA : ↥A ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNK
      have hAcard : Nat.card ↥A = Nat.card ↥N := Nat.card_congr eA.toEquiv
      have : IsMulCommutative ↥A := isMulCommutative_of_mulEquiv eA
      have hKcard : Nat.card ↥K = Nat.card ↥N * Nat.card ↥J := by
        rw [hK, natCard_comap_of_surjective (QuotientGroup.mk'_surjective N) J,
          QuotientGroup.ker_mk']
      have hAindex : A.index = Nat.card ↥J := by
        have h := Subgroup.card_mul_index A
        rw [hAcard, hKcard] at h
        exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
      have hcop : (Nat.card ↥A).Coprime A.index := by
        rw [hAcard, hAindex]
        exact (hJ.natCard.coprime_of_compl hNpi' Nat.card_pos.ne' Nat.card_pos.ne').symm
      obtain ⟨H', hH'⟩ := exists_isComplement'_of_coprime_index hcop
      have hmapA : A.map K.subtype = N := by
        rw [hA, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hNK]
      have hsup : K = N ⊔ H'.map K.subtype := by
        have h := congrArg (Subgroup.map K.subtype) hH'.sup_eq_top
        rw [Subgroup.map_sup, hmapA, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
        exact h.symm
      have hinf : N ⊓ H'.map K.subtype = ⊥ := by
        have h := congrArg (Subgroup.map K.subtype) (disjoint_iff.1 hH'.disjoint)
        rwa [Subgroup.map_inf _ _ _ K.subtype_injective, hmapA, Subgroup.map_bot] at h
      exact ⟨H'.map K.subtype, isHallSubgroup_of_comap_of_sup_eq hNpi' hJ hK hsup hinf⟩

theorem exists_isHallSubgroup {X : Type*} [Group X] [Finite X] [Group.IsSolvable X] (π : Set ℕ) :
    ∃ H : Subgroup X, IsHallSubgroup π H :=
  exists_isHallSubgroup_aux π (Nat.card X) X le_rfl

theorem exists_isPiNumber_natCard_and_isPiNumber_natCard_div {X : Type*} [Group X] [Finite X]
    [Group.IsSolvable X] (π : Set ℕ) :
    ∃ H : Subgroup X, IsPiNumber π (Nat.card H) ∧ IsPiNumber πᶜ (Nat.card X / Nat.card H) := by
  obtain ⟨H, hH⟩ := exists_isHallSubgroup (X := X) π
  exact ⟨H, isHallSubgroup_iff_natCard_div.1 hH⟩

theorem exists_coprime_natCard_index {X : Type*} [Group X] [Finite X] [Group.IsSolvable X]
    (π : Set ℕ) : ∃ H : Subgroup X, IsHallSubgroup π H ∧ (Nat.card H).Coprime H.index := by
  obtain ⟨H, hH⟩ := exists_isHallSubgroup (X := X) π
  exact ⟨H, hH, hH.coprime_natCard_index⟩

theorem exists_isHallSubgroup_ge_of_normal {X : Type*} [Group X] [Finite X] [Group.IsSolvable X]
    {π : Set ℕ} {N : Subgroup X} [N.Normal] (hN : IsPiNumber π (Nat.card N)) :
    ∃ H : Subgroup X, IsHallSubgroup π H ∧ N ≤ H := by
  obtain ⟨H, hH⟩ := exists_isHallSubgroup (X := X) π
  exact ⟨H, hH, hH.normal_le hN⟩

end CFSG.FeitThompson

end
