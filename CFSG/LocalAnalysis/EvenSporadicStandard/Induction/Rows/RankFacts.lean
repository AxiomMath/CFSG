module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Parts
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic

theorem pRank_two_eq_of_mulEquiv' {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    CFSG.pRank 2 X = CFSG.pRank 2 Y := CFSG.pRank_congr_of_mulEquiv e 2

theorem three_le_pRank_of_eight' {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    (hE : CFSG.IsElementaryAbelian 2 E) (hcard : Nat.card E = 8) : 3 ≤ CFSG.pRank 2 X := by
  apply le_csSup
  · refine ⟨Nat.card X, ?_⟩
    rintro r ⟨B, -, hB⟩
    have h1 : r < 2 ^ r := Nat.lt_two_pow_self
    have h2 : Nat.card B ≤ Nat.card X := Subgroup.card_le_card_group B
    omega
  · exact ⟨E, hE, by rw [hcard]; norm_num⟩

theorem three_le_pRank_of_oddCentralExt {D X : Type} [Group D] [Finite D] [Group X]
    (hD : 3 ≤ CFSG.pRank 2 D) (hX : IsOddCentralExt D X) : 3 ≤ CFSG.pRank 2 X := by
  obtain ⟨-, π, hπs, -, hodd⟩ := hX
  have hker : Finite π.ker := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have e : (X ⧸ π.ker) ≃* D := QuotientGroup.quotientKerEquivOfSurjective π hπs
  have hq : Finite (X ⧸ π.ker) := Finite.of_equiv D e.symm.toEquiv
  have : Finite X := Finite.of_subgroup_quotient π.ker
  rw [← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two π.ker
    (by rintro ⟨k, hk⟩; rw [hk] at hodd; exact absurd hodd (by simp)),
    pRank_two_eq_of_mulEquiv' e]
  exact hD

theorem three_le_pRank_of_isLS {s : TauCeti.SporadicName} (hfin : Finite (Carrier s))
    (hs : ∀ (Y : Type) [Group Y], IsSporadic Y s → 3 ≤ CFSG.pRank 2 Y) {X : Type} [Group X]
    (hX : IsLS [s] X) : 3 ≤ CFSG.pRank 2 X := by
  obtain ⟨s', hs', -, hodd, hY⟩ := hX
  rcases List.mem_singleton.1 hs' with rfl
  obtain ⟨f⟩ := hY
  have hZ : Finite (center X) := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have hq : Finite (X ⧸ center X) := Finite.of_equiv _ f.symm.toEquiv
  have : Finite X := Finite.of_subgroup_quotient (center X)
  rw [← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two (center X)
    (by rintro ⟨k, hk⟩; rw [hk] at hodd; exact absurd hodd (by simp))]
  exact hs _ ⟨f⟩

end CFSG.EvenSporadicStandard.Induction
