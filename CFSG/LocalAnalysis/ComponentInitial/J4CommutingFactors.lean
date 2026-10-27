module

public import CFSG.LocalAnalysis.ComponentInitial.SimpleOrder33792
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.Sporadic.J4
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalogBase

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem dvd_of_sq_dvd_sq_mul_squarefree {d s Q : ℕ} (hQ : Squarefree Q) (hs : s ≠ 0)
    (h : d ^ 2 ∣ s ^ 2 * Q) : d ∣ s := by
  obtain ⟨d', s', hcop, hd, hs'⟩ := Nat.exists_coprime d s
  have hg : 0 < Nat.gcd d s := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hs)
  generalize Nat.gcd d s = g at hd hs' hg
  subst hd hs'
  rw [mul_pow, mul_pow, mul_right_comm] at h
  have h' : d' ^ 2 ∣ Q :=
    (Nat.Coprime.pow 2 2 hcop).dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_right (pow_pos hg 2) h)
  have hunit : d' = 1 := Nat.isUnit_iff.mp (hQ d' (by rwa [sq] at h'))
  rw [hunit, one_mul]
  exact dvd_mul_left g s'

theorem dvd_33792_of_sq_dvd {m : ℕ} (h : m ^ 2 ∣ 86775571046077562880) : m ∣ 33792 := by
  have hQ : Squarefree 75992317170 := by
    rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
    simp
  refine dvd_of_sq_dvd_sq_mul_squarefree hQ (by norm_num) ?_
  rwa [show (33792 : ℕ) ^ 2 * 75992317170 = 86775571046077562880 by norm_num]

theorem central_quotient_excludes_equal_commuting_quasisimple_factors_of_card_quotient_dvd
    {L : Type*} [Group L] [Finite L] {A : Subgroup L} (hA : A ≤ center L)
    (hcard : Nat.card (L ⧸ A) ∣ 86775571046077562880) :
    ¬ ∃ J K : Subgroup L, CFSG.Assembly.IsQuasisimple J ∧ CFSG.Assembly.IsQuasisimple K ∧
      ⁅J, K⁆ = ⊥ ∧ Nat.card (J ⧸ center J) = Nat.card (K ⧸ center K) := by
  rintro ⟨J, K, hJ, hK, hJK, hJKcard⟩
  have hsq : Nat.card (J ⧸ center J) ^ 2 ∣ Nat.card (L ⧸ A) := by
    have h := (commuting_quasisimple_factors_central_quotient_divisor hJ hK hJK hA).1
    rwa [← hJKcard, ← sq] at h
  obtain ⟨-, hs, hnab⟩ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).1 hJ
  exact no_nonabelian_simple_order_dividing_33792 hs hnab (dvd_33792_of_sq_dvd (hsq.trans hcard))

theorem j4_central_quotient_excludes_equal_commuting_quasisimple_factors_of_orderHyp
    (hJ4 : CFSG.SectionRank.J4OrderHyp) {L : Type*} [Group L] [Finite L] {A : Subgroup L}
    [A.Normal] (hA : A ≤ center L) (e : L ⧸ A ≃* CFSG.Blueprint.NativeSporadic.J4) :
    ¬ ∃ J K : Subgroup L, CFSG.Assembly.IsQuasisimple J ∧ CFSG.Assembly.IsQuasisimple K ∧
      ⁅J, K⁆ = ⊥ ∧ Nat.card (J ⧸ center J) = Nat.card (K ⧸ center K) :=
  central_quotient_excludes_equal_commuting_quasisimple_factors_of_card_quotient_dvd hA
    ((Nat.card_congr e.toEquiv).dvd.trans hJ4)

theorem j4_central_quotient_excludes_equal_commuting_quasisimple_factors {L : Type*} [Group L]
    [Finite L] {A : Subgroup L} [A.Normal] (hA : A ≤ center L)
    (e : L ⧸ A ≃* CFSG.Blueprint.NativeSporadic.J4) :
    ¬ ∃ J K : Subgroup L, CFSG.Assembly.IsQuasisimple J ∧ CFSG.Assembly.IsQuasisimple K ∧
      ⁅J, K⁆ = ⊥ ∧ Nat.card (J ⧸ center J) = Nat.card (K ⧸ center K) :=
  j4_central_quotient_excludes_equal_commuting_quasisimple_factors_of_orderHyp
    (by rw [CFSG.SectionRank.J4OrderHyp, CFSG.Sporadic.J4.card_J4]) hA e

end CFSG.LocalAnalysis.ComponentInitial
