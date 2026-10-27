module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Crit
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem ivk93m12_two_pow_six_dvd_of_aut {J : Type} [Group J] [Finite J]
    (hout : ¬ 2 ∣ Nat.card (Outer J)) (h : 2 ^ 6 ∣ Nat.card (MulAut J)) : 2 ^ 6 ∣ Nat.card J := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner J)
  have hcop : Nat.Coprime (2 ^ 6) (Nat.card (Outer J)) :=
    Nat.Coprime.pow_left 6 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hout)
  rw [h1] at h
  have h2 : 2 ^ 6 ∣ Nat.card ↥(inner J) := hcop.dvd_of_dvd_mul_left h
  have h3 : Nat.card ↥(inner J) ∣ Nat.card J :=
    Subgroup.card_dvd_of_surjective (f := (MulAut.conj : J →* MulAut J).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  exact h2.trans h3

theorem ivk93m12_ree :
    ∀ f : ℕ, Ivk93M12Empty (fun X _ => LieModel X .twistedG2 0 3 f) := by
  intro f J _ _ hJ y D
  have hR : ReeTitsModel J .twistedG2 3 f := by
    rcases hJ with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
    · exact absurd hh (by decide)
    · exact absurd hh (by decide)
    · exact hR
    · exact absurd hh (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hout : ¬ 2 ∣ Nat.card (Outer J) := by
    intro h2
    have ho := (CFSG.LieType.Ree.SuzukiReeOuterTwoPart.small_Ree_case hR).1
    have hne : Nat.card (Outer J) ≠ 0 := Nat.card_pos.ne'
    have h1 := (Nat.prime_two.pow_dvd_iff_dvd_ordProj (k := 1) hne).1 (by simpa using h2)
    rw [ho] at h1
    omega
  have hC := GHInv.ordProj_two_card_centralizer_ree hR D.orderOf_eq_two
  have hCne : Nat.card ↥(Subgroup.centralizer ({y} : Set J)) ≠ 0 := Nat.card_pos.ne'
  have hnot : ¬ 2 ^ 6 ∣ Nat.card J := by
    intro h64
    obtain ⟨T⟩ : Nonempty (Sylow 2 J) := inferInstance
    have hcardT := Sylow.card_eq_multiplicity T
    have hle : 6 ≤ (Nat.card J).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h64
    have hdvd : 2 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({y} : Set J)) := by
      refine (pow_dvd_pow 2 hle).trans ?_
      rw [← hcardT]
      exact D.card_sylow_dvd_cent T
    have h8 := (Nat.prime_two.pow_dvd_iff_dvd_ordProj hCne).1 hdvd
    rw [hC] at h8
    have := Nat.le_of_dvd (by norm_num) h8
    omega
  exact hnot (ivk93m12_two_pow_six_dvd_of_aut hout D.two_pow_six_dvd_card_aut)

end CFSG.GH74.GLS.IVK.Proofs2
