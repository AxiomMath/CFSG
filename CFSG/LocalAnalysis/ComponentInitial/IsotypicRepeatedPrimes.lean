module

public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem three_le_card_primeFactors_of_isQuasisimple {J : Type*} [Group J] [Finite J]
    (hJ : CFSG.Assembly.IsQuasisimple J) : 3 ≤ (Nat.card (J ⧸ center J)).primeFactors.card := by
  have : Group.IsPerfect J := Group.isPerfect_def.2 hJ.1
  have : Group.IsPerfect (J ⧸ center J) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center J))
      (QuotientGroup.mk'_surjective _)
  have : IsSimpleGroup (J ⧸ center J) := hJ.2
  by_contra h
  push Not at h
  exact Group.IsPerfect.not_isSolvable (J ⧸ center J)
    (isSolvable_of_card_primeFactors_le_two (by omega))

theorem commuting_isotypic_quasisimple_factors_three_repeated_primes {L : Type*} [Group L]
    [Finite L] {J K A : Subgroup L} (hJ : CFSG.Assembly.IsQuasisimple J)
    (_hK : CFSG.Assembly.IsQuasisimple K) (hJK : ⁅J, K⁆ = ⊥)
    (hiso : Nonempty (J ⧸ center J ≃* K ⧸ center K)) (hA : A ≤ center L) :
    3 ≤ {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card (L ⧸ A)}.ncard := by
  obtain ⟨e⟩ := hiso
  have hsq := card_quotient_center_sq_dvd hJK hA (Nat.card_congr e.toEquiv)
  have h3 := three_le_card_primeFactors_of_isQuasisimple hJ
  have hn : Nat.card (L ⧸ A) ≠ 0 := Nat.card_pos.ne'
  have hsub : ((Nat.card (J ⧸ center J)).primeFactors : Set ℕ) ⊆
      {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card (L ⧸ A)} := by
    intro r hr
    rw [Finset.mem_coe, Nat.mem_primeFactors] at hr
    exact ⟨hr.1, (pow_dvd_pow_of_dvd hr.2.1 2).trans hsq⟩
  have hfin : {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card (L ⧸ A)}.Finite := by
    refine (Set.finite_Iic (Nat.card (L ⧸ A))).subset fun r hr => ?_
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hr.2
    have hr1 : r ≤ r ^ 2 := Nat.le_self_pow (by norm_num) r
    exact hr1.trans hle
  calc 3 ≤ (Nat.card (J ⧸ center J)).primeFactors.card := h3
    _ = ((Nat.card (J ⧸ center J)).primeFactors : Set ℕ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

end CFSG.LocalAnalysis.ComponentInitial
