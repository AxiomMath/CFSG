module

public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6.Prod

section Cover

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem dvd_card_of_cover {n : ℕ} (hX : IsDoubleCoverOfAlt X n) (hn : 4 ≤ n) :
    2 ^ 3 ∣ Nat.card X ∧ 3 ∣ Nat.card X := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hX
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h1 : Nat.card (X ⧸ center X) = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp
  have h2 : Nat.card X = n.factorial := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X), h1, hZ]
    exact Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) (by omega))
  have h4 := Nat.factorial_dvd_factorial hn
  have e4 : Nat.factorial 4 = 24 := by decide
  rw [e4] at h4
  rw [h2]
  exact ⟨(show 2 ^ 3 ∣ 24 by norm_num).trans h4, (show 3 ∣ 24 by norm_num).trans h4⟩

theorem oPrimeResidual_eq_top_of_cover {n : ℕ} (hX : IsDoubleCoverOfAlt X n) (hn : 4 ≤ n) :
    oPrimeResidual 2 X = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hX.1
    (oPrimeResidual_normal 2 X) with h | h
  · exact h
  · exfalso
    obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 3) (dvd_card_of_cover hX hn).1
    have hWle : W ≤ oPrimeResidual 2 X := by
      intro w hw
      apply Subgroup.subset_closure
      refine ⟨3, ?_⟩
      have h1 : orderOf (⟨w, hw⟩ : W) ∣ 2 ^ 3 := by rw [← hW]; exact orderOf_dvd_natCard _
      have h2 : (⟨w, hw⟩ : W) ^ (2 ^ 3) = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
      have := congrArg Subtype.val h2
      simpa using this
    have hle := Subgroup.card_le_of_le (hWle.trans h)
    rw [hW, hX.2.1] at hle
    norm_num at hle

theorem oResidual_eq_top_of_cover {n : ℕ} (hX : IsDoubleCoverOfAlt X n) (hn : 4 ≤ n) :
    oResidual 2 X = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hX.1
    (oResidual_normal 2 X) with h | h
  · exact h
  · exfalso
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 (dvd_card_of_cover hX hn).2
    have hcop : Nat.Coprime (orderOf g) 2 := by rw [hg]; norm_num
    have hgmem : g ∈ oResidual 2 X := Subgroup.subset_closure hcop
    have hgc : g ∈ center X := h hgmem
    have hdvd : orderOf g ∣ Nat.card (center X) := by
      have := orderOf_dvd_natCard (⟨g, hgc⟩ : center X)
      rwa [Subgroup.orderOf_mk] at this
    rw [hg, hX.2.1] at hdvd
    norm_num at hdvd

theorem oPrimePResidual_eq_top_of_cover {n : ℕ} (hX : IsDoubleCoverOfAlt X n) (hn : 4 ≤ n) :
    oPrimePResidual 2 X = ⊤ := by
  rw [oPrimePResidual_eq_oResidual Nat.prime_two (oPrimeResidual_eq_top_of_cover hX hn)]
  exact oResidual_eq_top_of_cover hX hn

end Cover

end CFSG.GH74.GLS.Stage1.Thm4
