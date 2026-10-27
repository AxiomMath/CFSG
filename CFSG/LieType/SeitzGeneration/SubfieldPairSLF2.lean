module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnPair

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

private theorem charP_two_of_card_subfield {K : Type} [Field K] {k : Subfield K}
    (hk : Nat.card k = 2) : CharP K 2 := by
  have hfin : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have := Fintype.ofFinite k
  have hq : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card]; exact hk
  have hc : CharP k (ringChar k) := ringChar.charP k
  obtain ⟨m, hpr, hm⟩ := FiniteField.card k (ringChar k)
  have hdvd : ringChar k ∣ 2 := by
    rw [hq] at hm
    rw [hm]
    exact dvd_pow_self _ m.ne_zero
  have h2 : ringChar k = 2 := (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp hdvd
  have : CharP k 2 := h2 ▸ hc
  exact charP_of_injective_ringHom (f := k.subtype) Subtype.val_injective 2

theorem subfieldPairSLF2_holds :
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K) (p : ℕ), p.Prime → p ≠ 2 →
      Nat.card K = Nat.card k ^ p → Nat.card k = 2 → ∀ n : ℕ, 3 ≤ n → ∀ A : GL (Fin n) K,
        (slSub n k).map (slConjugation n K A).toMonoidHom ≠ slSub n k →
          Subgroup.closure ((slSub n k : Set (SpecialLinearGroup (Fin n) K)) ∪
            ((slSub n k).map (slConjugation n K A).toMonoidHom :
              Set (SpecialLinearGroup (Fin n) K))) = ⊤ := by
  intro K _ _ k p hp hp2 hK hk n hn A hne
  have : CharP K 2 := charP_two_of_card_subfield hk
  exact CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.subfieldPairSL_two_gen
    k hp hK hp2 hn A hne

end CFSG.LieType.SeitzGeneration
