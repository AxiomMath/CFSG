module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Standard

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

variable [Finite H]

theorem mem_normalizer_of_fixes {M K' R : Subgroup H}
    (hM : IsCompIn M (centralizer (R : Set H))) (hK'M : K' ≤ M)
    (hK'q : CFSG.IsQuasisimple ↥K') {n : H} (hnR : n ∈ normalizer (R : Set H))
    (hnK : n ∈ centralizer (K' : Set H)) : n ∈ normalizer (M : Set H) := by
  have hMn : IsCompIn (M.map (MulAut.conj n).toMonoidHom) (centralizer (R : Set H)) :=
    isCompIn_map_conj_of_mem_normalizer hM (mem_normalizer_centralizer_of_mem_normalizer hnR)
  by_cases heq : M.map (MulAut.conj n).toMonoidHom = M
  · exact mem_normalizer_iff_map_conj_eq.2 heq
  · exfalso
    have hKn : K' ≤ M.map (MulAut.conj n).toMonoidHom := by
      intro k hk
      refine ⟨k, hK'M hk, ?_⟩
      show n * k * n⁻¹ = k
      have := Subgroup.mem_centralizer_iff.1 hnK k hk
      calc n * k * n⁻¹ = (k * n) * n⁻¹ := by rw [← this]
        _ = k := by group
    refine not_forall_commute_of_isQuasisimple hK'q fun a ha b hb => ?_
    exact hMn.commute_of_ne hM heq a (hKn ha) b (hK'M hb)

theorem even_card_of_three_le_pRank {X : Type*} [Group X] (h : 3 ≤ CFSG.pRank 2 X) :
    Even (Nat.card X) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hub : (3 : ℕ) ≤ 0 := by
    refine h.trans (csSup_le' fun r hr => ?_)
    obtain ⟨A, -, hA⟩ := hr
    by_contra hr0
    have h2 : 2 ∣ Nat.card A := by
      rw [hA]
      exact dvd_pow_self 2 (by omega)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2
      (h2.trans (Subgroup.card_subgroup_dvd_card A)))
  omega

end CFSG.EvenSporadicStandard.Induction
