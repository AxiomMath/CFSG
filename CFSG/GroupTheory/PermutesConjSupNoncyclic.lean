module

public import CFSG.GroupTheory.PermutesConjSupElemAbelian
public import CFSG.GroupTheory.ElemAbelianRank

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

theorem exists_noncyclic_permutes_sup_conj {H : Type*} [Group H] [Finite H] {K T A : Subgroup H}
    (hAK : A ≤ K)
    (hcomm : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom ≠ K →
      ∀ x ∈ K, ∀ y ∈ K.map (MulAut.conj t).toMonoidHom, Commute x y)
    (hperm : (A : Set H) * ((T ⊓ normalizer (K : Set H) : Subgroup H) : Set H) =
      ((T ⊓ normalizer (K : Set H) : Subgroup H) : Set H) * A)
    (hKne : ∃ t ∈ T, K.map (MulAut.conj t).toMonoidHom ≠ K)
    (hAnc : ¬ A ≤ (Subgroup.center ↥K).map K.subtype)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) :
    ∃ X : Subgroup H, A ≤ X ∧ (X : Set H) * T = T * X ∧
      (∀ n : ℕ, (∀ a ∈ A, a ^ n = 1) → ∀ x ∈ X, x ^ n = 1) ∧
      (∀ p : ℕ, IsPGroup p A → IsPGroup p X) ∧ ¬ IsCyclic ↥X := by
  by_cases hAcyc : IsCyclic ↥A
  · have hAcard : Nat.card ↥A = 3 := by
      have hdiv : Nat.card ↥A ∣ 3 := by
        rw [← IsCyclic.exponent_eq_card]
        exact Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
          Subtype.ext (by simpa using hA3 (a : H) a.2)
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdiv with h | h
      · exact absurd h (fun h' => hAnc (Subgroup.eq_bot_of_card_eq A h' ▸ bot_le))
      · exact h
    obtain ⟨X, hAX, -, hXT, hXab, hXrk⟩ :=
      exists_elemAbelian_permutes_sup_conj Nat.prime_three hAK hcomm hperm hKne hAnc hAcard
        (Rbar := ⊤) le_top (fun t _ => Subgroup.mem_normalizer_iff.2 fun h => by simp)
    refine ⟨X, hAX, hXT, fun n hn x hx => ?_, fun p hp x => ?_, fun hXcyc => ?_⟩
    · obtain ⟨m, rfl⟩ : 3 ∣ n := by
        rw [← hAcard, ← IsCyclic.exponent_eq_card]
        exact Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
          Subtype.ext (by simpa using hn (a : H) a.2)
      rw [pow_mul, hXab.2 x hx, one_pow]
    · obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥A)
      obtain ⟨k, hk⟩ := hp g
      obtain ⟨m, hm⟩ : 3 ∣ p ^ k := by
        rw [← hAcard, ← hg]
        exact orderOf_dvd_of_pow_eq_one hk
      refine ⟨k, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, hm, pow_mul, hXab.2 (x : H) x.2, one_pow, Subgroup.coe_one]
    · have hdvd : Nat.card ↥X ∣ 3 := by
        rw [← IsCyclic.exponent_eq_card]
        exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (by simpa using hXab.2 (x : H) x.2)
      have h9 : 9 ≤ Nat.card ↥X := by
        rw [card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hXab]
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ CFSG.Open.pRank 3 X := Nat.pow_le_pow_right (by norm_num) hXrk
      have h3 := Nat.le_of_dvd (by norm_num) hdvd
      omega
  · obtain ⟨X, hAX, hXT, hexp, hp⟩ := exists_permutes_sup_conj hAK hcomm hperm
    exact ⟨X, hAX, hXT, hexp, hp, fun hX => hAcyc
      (@isCyclic_of_injective ↥A ↥X _ _ hX (Subgroup.inclusion hAX)
        (Subgroup.inclusion_injective hAX))⟩

end CFSG.GroupTheory

end
