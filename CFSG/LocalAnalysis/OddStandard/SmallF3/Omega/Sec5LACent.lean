module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem sec5la_aux_finrank_commSp_eq {t : OGroup Q} {r : ℕ} {α : ℤˣ}
    (hty : invType t = (r, α)) : Module.finrank (ZMod 3) (commSp t) = r := by
  have h := congrArg Prod.fst hty
  simpa only [invType, invDim] using h

private theorem sec5la_aux_quadSign_commSp_eq {t : OGroup Q} {r : ℕ} {α : ℤˣ}
    (hty : invType t = (r, α)) : quadSign (Q.restrict (commSp t)) = α := by
  have h := congrArg Prod.snd hty
  simpa only [invType, invSign] using h

private theorem sec5la_aux_quadSign_fixSp_eq (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {t : OGroup Q}
    (htt : t * t = 1) (hty : invType t = (4, 1)) :
    quadSign (Q.restrict (fixSp t)) = -1 := by
  have h := quadSign_fixSp_eq hQ htt
  have hr : invDim t = 4 := congrArg Prod.fst hty
  have hα : invSign t = 1 := congrArg Prod.snd hty
  have hpow : ((-1 : ℤˣ) ^ (4 * (6 - 4))) = 1 := by
    rw [show 4 * (6 - 4) = 2 * 4 by norm_num, pow_mul]
    have h2 : (-1 : ℤˣ) ^ 2 = 1 := by norm_num
    rw [h2, one_pow]
  rw [hsgn, hα, hr, hdim] at h
  simpa [hpow] using h

theorem sec5la_natCard_centralizer_type_four_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) {u : OGroup Q}
    (huu : u * u = 1) (hty : invType u = (4, 1)) :
    Nat.card (Subgroup.centralizer ({u} : Set (OGroup Q))) = 2 ^ 10 * 3 ^ 2 := by
  have hdimC : Module.finrank (ZMod 3) (commSp u) = 4 := sec5la_aux_finrank_commSp_eq hty
  have hsgnC : quadSign (Q.restrict (commSp u)) = 1 := sec5la_aux_quadSign_commSp_eq hty
  have hdimU : Module.finrank (ZMod 3) (fixSp u) = 2 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) u
    omega
  have hsgnU : quadSign (Q.restrict (fixSp u)) = -1 :=
    sec5la_aux_quadSign_fixSp_eq hQ hdim hs huu hty
  rw [natCard_centralizer_involution hQ huu,
    natCard_oGroup_two_minus (nondegenerate_restrict_fixSp hQ huu) hdimU hsgnU,
    natCard_oGroup_four_plus (nondegenerate_restrict_commSp hQ huu) hdimC hsgnC]
  norm_num

theorem sec5la_eq_one_of_commute_pow_eq_one (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) {u : OGroup Q}
    (huu : u * u = 1) (hty : invType u = (4, 1)) {n : ℕ} (hn : Nat.Coprime n 6)
    {o : OGroup Q} (hou : o * u = u * o) (hon : o ^ n = 1) : o = 1 := by
  have hoH : o ∈ Subgroup.centralizer ({u} : Set (OGroup Q)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hou.symm
  have hcardH : Nat.card (Subgroup.centralizer ({u} : Set (OGroup Q))) = 2 ^ 10 * 3 ^ 2 :=
    sec5la_natCard_centralizer_type_four_plus hQ hdim hs huu hty
  have hcop : Nat.Coprime n (2 ^ 10 * 3 ^ 2) := by
    have h2 : Nat.Coprime n 2 :=
      Nat.Coprime.coprime_dvd_right (show 2 ∣ 6 by norm_num) hn
    have h3 : Nat.Coprime n 3 :=
      Nat.Coprime.coprime_dvd_right (show 3 ∣ 6 by norm_num) hn
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 10 h2) (Nat.Coprime.pow_right 2 h3)
  have hdvd1 : orderOf o ∣ 1 := by
    have h : orderOf o ∣ Nat.gcd n (2 ^ 10 * 3 ^ 2) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hon)
        (by rw [← hcardH]; exact Subgroup.orderOf_dvd_natCard _ hoH)
    rwa [hcop.gcd_eq_one] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)

end CFSG.OddStandard.SmallF3.Omega
