module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviNode

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabHub CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

theorem nodeLevi_su_short {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) :
    NodeLevi (rootDatum hF n) k :=
  nodeLevi_of_equiv_sl2 (rankOneShortEquiv (hσ := unitaryInvolution_involutive hF) hk).symm

theorem nodeLevi_su_last_even (he : Even n) {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) :
    NodeLevi (rootDatum hF n) k := by
  obtain ⟨z, hz0, hz⟩ := exists_unitaryInvolution_eq_neg hF
  have := Fintype.ofFinite F
  have e := (hypEquiv (p := 2) (f := f) hz0 (by simpa using hz)).trans
    (rankOneLastEvenEquiv hF he hk).symm
  exact nodeLevi_of_equiv_sl2 e

theorem nodeLevi_su_last_odd (ho : ¬Even n) {k : Fin (n / 2)}
    (hk : ¬k.val + 1 < n / 2) : NodeLevi (rootDatum hF n) k := by
  have e := rankOneLastOddEquiv (p := 2) (f := f) hF ho hk
  by_cases hf : f = 1
  · subst hf
    left
    have hc := card_SU_three (p := 2) (f := 1) hF
    have hs : Group.IsSolvable (SU (unitaryInvolution F 2 1) 3) := by
      have := Fintype.ofFinite (SU (unitaryInvolution F 2 1) 3)
      refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        (p := 2) (q := 3) (a := 3) (b := 3) Nat.prime_two Nat.prime_three (by norm_num) ?_
      rw [← Nat.card_eq_fintype_card, hc]
      norm_num
    have := hs
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · right
    have hf2 : 2 ≤ f := by
      rcases Nat.lt_or_ge f 2 with h | h
      · exfalso
        have hf0 : f ≠ 0 := by
          rintro rfl
          have := Finite.one_lt_card (α := F)
          rw [hF] at this
          simp at this
        omega
      · exact h
    have hnq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := by
      intro h
      have : 2 ^ f = 2 := (Prod.mk.inj h).2
      have : f = 1 := by
        have := Nat.pow_right_injective (le_refl 2) (show 2 ^ f = 2 ^ 1 by simpa using this)
        exact this
      exact hf this
    have hq := isQuasisimple_SU (p := 2) (f := f) hF (le_refl 3) hnq
    exact isQuasisimple_of_mulEquiv_open e.symm ⟨hq.1.commutator_eq_top, hq.2.1⟩

theorem nodeLevi_su (i : Fin (n / 2)) : NodeLevi (rootDatum hF n) i := by
  by_cases hk : i.val + 1 < n / 2
  · exact nodeLevi_su_short hF hk
  · by_cases he : Even n
    · exact nodeLevi_su_last_even hF he hk
    · exact nodeLevi_su_last_odd hF he hk

end CFSG.AGLEmbeddingD2.Tits.GN516

