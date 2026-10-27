module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddShape
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddSp

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.Blueprint CFSG.GH74.GLS.IVK.GHInv CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

theorem gomiOdd_exists_centralizer_elem {M : Type} [Group M] [Finite M] (E : Subgroup M)
    (hEcard : Nat.card E = 2 ^ 6) (hEsq : ∀ x ∈ E, x * x = 1) :
    ∃ z : M, orderOf z = 2 ∧ ∃ E' : Subgroup ↥(Subgroup.centralizer ({z} : Set M)),
      Nat.card E' = 2 ^ 6 ∧ ∀ x ∈ E', x * x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEcard
    norm_num at hEcard
  obtain ⟨⟨z, hzE⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (hEsq _ (E.mul_mem hx hy))).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by
        rw [inv_eq_of_mul_eq_one_right (hEsq x hx), inv_eq_of_mul_eq_one_right (hEsq y hy)]
  have hEC : E ≤ Subgroup.centralizer ({z} : Set M) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm x hx z hzE
  refine ⟨z, orderOf_eq_prime (by rw [pow_two]; exact hEsq z hzE) hz1', E.subgroupOf _, ?_, ?_⟩
  · rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv
  · intro x hx
    exact Subtype.ext (hEsq _ hx)

theorem gomiOdd_false_of_g2 {M : Type} [Group M] [Finite M] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hM : LieModel M .G2 0 p f) (E : Subgroup M)
    (hEcard : Nat.card E = 2 ^ 6) (hEsq : ∀ x ∈ E, x * x = 1) : False := by
  obtain ⟨z, hz, E', hE'card, hE'sq⟩ := gomiOdd_exists_centralizer_elem E hEcard hEsq
  obtain ⟨F, hF, hFin, S, hcard, -⟩ := exists_shape_G2 hp hp2 hM z hz
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 := gomiOdd_two_ne_zero hodd
  exact gomiOdd_false_of_shape h2 h2 S E' hE'card hE'sq

theorem gomiOdd_false_of_d4 {M : Type} [Group M] [Finite M] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hM : LieModel M .trialityD4 0 p f) (E : Subgroup M)
    (hEcard : Nat.card E = 2 ^ 6) (hEsq : ∀ x ∈ E, x * x = 1) : False := by
  obtain ⟨z, hz, E', hE'card, hE'sq⟩ := gomiOdd_exists_centralizer_elem E hEcard hEsq
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hc₁, hc₂, -⟩ := exists_shape_D4 hp hp2 hM z hz
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hodd₁ : Odd (Nat.card F₁) := by
    rw [hc₁]
    exact hq.pow
  have hodd₂ : Odd (Nat.card F₂) := by
    rw [hc₂]
    exact hq
  exact gomiOdd_false_of_shape (gomiOdd_two_ne_zero hodd₁) (gomiOdd_two_ne_zero hodd₂) S E'
    hE'card hE'sq

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
