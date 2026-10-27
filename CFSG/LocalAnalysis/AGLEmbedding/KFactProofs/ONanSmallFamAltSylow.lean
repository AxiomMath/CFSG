module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFam

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open Equiv

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem pow_eq_one_of_pow_pow_eq_one (hp : p.Prime) (hp2 : p ≠ 2) {g : Perm (Fin (2 * p))}
    {k : ℕ} (hg : g ^ p ^ k = 1) : g ^ p = 1 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rw [← orderOf_dvd_iff_pow_eq_one, ← Perm.lcm_cycleType]
  refine Multiset.lcm_dvd.2 fun l hl => ?_
  have h1 : l ∣ p ^ k := (Perm.dvd_of_mem_cycleType hl).trans (orderOf_dvd_of_pow_eq_one hg)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 h1
  have h2 : p ^ j ≤ 2 * p :=
    (Perm.le_card_support_of_mem_cycleType hl).trans
      ((Finset.card_le_univ _).trans (by simp))
  by_cases hj : j ≤ 1
  · exact (pow_dvd_pow p hj).trans (by simp)
  · exfalso
    have h3 : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
    nlinarith

@[expose] def altPermEmbed (e : K ≃* alternatingGroup (Fin (2 * p))) : K →* Perm (Fin (2 * p)) :=
  (alternatingGroup (Fin (2 * p))).subtype.comp e.toMonoidHom

omit [Finite K] in
theorem altPermEmbed_injective (e : K ≃* alternatingGroup (Fin (2 * p))) :
    Function.Injective (altPermEmbed e) :=
  Subtype.val_injective.comp e.injective

omit [Finite K] in
theorem sign_altPermEmbed (e : K ≃* alternatingGroup (Fin (2 * p))) (k : K) :
    Perm.sign (altPermEmbed e k) = 1 :=
  Perm.mem_alternatingGroup.1 (e k).2

theorem isElemAbelian_map_sylow (hp : p.Prime) (hp2 : p ≠ 2)
    (e : K ≃* alternatingGroup (Fin (2 * p))) (S : Sylow p K) :
    IsElemAbelian p ((S : Subgroup K).map (altPermEmbed e)) ∧
      Nat.card ((S : Subgroup K).map (altPermEmbed e)) = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hEcard : Nat.card ((S : Subgroup K).map (altPermEmbed e)) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (altPermEmbed_injective e)]
    exact sylowSq_of_isAltTwoP hp hp2 ⟨e⟩ S
  refine ⟨⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hEcard, fun x hx => ?_⟩, hEcard⟩
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨n, hn⟩ := S.2 ⟨k, hk⟩
  refine pow_eq_one_of_pow_pow_eq_one hp hp2 (k := n) ?_
  rw [← map_pow]
  have h1 : k ^ p ^ n = 1 := congrArg Subtype.val hn
  rw [h1, map_one]

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
