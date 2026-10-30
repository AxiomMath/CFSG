module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.SixtyOrder
import CFSG.GH74.KGroups.A5
public import CFSG.Sporadic.Schreier.PairJ3Faithful
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.RankThree.PartTwo.Census.Sporadic.J3

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

private lemma ordA_one_eq (q : ℕ) :
    CFSG.Open.ordA 1 q = q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) := by
  norm_num [CFSG.Open.ordA, Finset.Icc_self]

theorem nonempty_mulEquiv_alternatingGroup_five_of_lieModel_card_sixty
    {X : Type} [Group X]
    {p f : ℕ} (hp : p.Prime) (hm : LieModel X .PSL 2 p f) (hc : Nat.card X = 60) :
    Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  have hcard := CFSG.GH74.card_of_lieModel_PSL (by norm_num) hm
  have hq : Open.ordA 1 (p ^ f) = 60 := hcard.symm.trans hc
  rw [ordA_one_eq] at hq
  have ha := hm.admissible
  have hf1 : 1 ≤ f := ha.2.1
  have hqne2 : p ^ f ≠ 2 := fun h => ha.2.2.2.1 (by rw [h])
  have hqne3 : p ^ f ≠ 3 := fun h => ha.2.2.2.2 (by rw [h])
  have hqge0 : 2 ≤ p ^ f := by
    have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  set q : ℕ := p ^ f with hqdef
  have h2 : q - 1 ∣ q ^ 2 - 1 := by
    refine ⟨q + 1, ?_⟩
    show q ^ 2 - 1 ^ 2 = (q - 1) * (q + 1)
    rw [Nat.pow_two_sub_pow_two, Nat.mul_comm]
  have hg_dvd : Nat.gcd 2 (q - 1) ∣ q * (q ^ 2 - 1) :=
    (Nat.gcd_dvd_right 2 (q - 1)).trans (h2.trans (dvd_mul_left _ _))
  have hgpos : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left (q - 1) (by norm_num)
  have hmul : q * (q ^ 2 - 1) = 60 * Nat.gcd 2 (q - 1) :=
    (Nat.div_eq_iff_eq_mul_left hgpos hg_dvd).1 hq
  have hgle : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left (q - 1) (by norm_num)
  have hgbound : q * (q ^ 2 - 1) ≤ 120 := by
    rw [hmul]
    nlinarith
  have hqle5 : q ≤ 5 := by
    by_contra h
    push Not at h
    have h36 : 36 ≤ q ^ 2 := by
      simpa [pow_two] using Nat.mul_self_le_mul_self h
    have h35 : 35 ≤ q ^ 2 - 1 := by omega
    have h210 : 210 ≤ q * (q ^ 2 - 1) := by
      calc 210 = 6 * 35 := by norm_num
        _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h h35
    omega
  have hq45 : q = 4 ∨ q = 5 := by omega
  rcases hq45 with hq4 | hq5
  · have hpf4 : p ^ f = 4 := by rw [← hqdef]; exact hq4
    have hpdvd : p ∣ 4 := by
      rw [← hpf4]
      exact dvd_pow_self p (n := f) (by omega)
    have hp_eq2 : p = 2 := by
      have h1 : p ∣ 2 ^ 2 := by simpa using hpdvd
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
    subst hp_eq2
    have hf_eq2 : f = 2 :=
      Nat.pow_right_injective (a := 2) (by norm_num)
        (by show (2 : ℕ) ^ f = 2 ^ 2; rw [hpf4])
    subst hf_eq2
    exact CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model X hm
  · have hpf5 : p ^ f = 5 := by rw [← hqdef]; exact hq5
    have hpdvd : p ∣ 5 := by
      rw [← hpf5]
      exact dvd_pow_self p (n := f) (by omega)
    have hp_eq5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hpdvd
    subst hp_eq5
    have hf_eq1 : f = 1 :=
      Nat.pow_right_injective (a := 5) (by norm_num)
        (by show (5 : ℕ) ^ f = 5 ^ 1; rw [hpf5])
    subst hf_eq1
    obtain ⟨e5⟩ := CFSG.GH74.KGroups.A5.equiv_of_lieModel25 hm
    exact ⟨e5.trans (MulEquiv.subgroupCongr CFSG.GH74.KGroups.A5.QP_eq_alt)⟩

section J3


theorem nonempty_mulEquiv_alternatingGroup_five_of_J3 {S : Type} [Group S] [Finite S]
    (e : S ≃* Carrier .J3) {t : S} (ht : orderOf t = 2)
    {B : Subgroup ↥(centralizer ({t} : Set S))} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : LieModel (↥B ⧸ center ↥B) .PSL 2 p f) :
    Nonempty (↥B ⧸ center ↥B ≃* alternatingGroup (Fin 5)) := by
  let φ : S ≃* ↥Sporadic.Schreier.j3P := e.trans Sporadic.Schreier.j3PermEquiv
  have hd := Subgroup.card_subgroup_dvd_card B
  rw [Nat.card_congr (CFSG.ComponentClassification.BMCase.gmatCentralizerEquiv φ t).toEquiv,
    CFSG.RankThree.PartTwo.Census.card_centralizer_j3P
      (by rw [MulEquiv.orderOf_eq]; exact ht)] at hd
  have hd1920 : Nat.card B ∣ 2 ^ 7 * 15 := by
    rw [show (2 : ℕ) ^ 7 * 15 = 1920 by norm_num]
    exact hd
  have hdvd : Nat.card (↥B ⧸ center ↥B) ∣ 2 ^ 7 * 15 :=
    (Subgroup.card_quotient_dvd_card (center ↥B)).trans hd1920
  have ho : CFSG.ComponentClassification.HarrisLit.T1.SporRow.OddLieOrder
      (Nat.card (↥B ⧸ center ↥B)) :=
    CFSG.ComponentClassification.HarrisLit.T1.SporRow.oddLieOrder_of_lieModel hp hp2 hm
  have h60 : Nat.card (↥B ⧸ center ↥B) = 60 :=
    CFSG.ComponentClassification.HarrisLit.T1.SporRow.OddLieOrder.eq_sixty_of_dvd ho hdvd
  exact nonempty_mulEquiv_alternatingGroup_five_of_lieModel_card_sixty hp hm h60

end J3

end CFSG.OddStandard.L2Ree
