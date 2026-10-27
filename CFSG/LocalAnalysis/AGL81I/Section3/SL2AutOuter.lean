module

public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

theorem card_outer_SL2_dvd_two_of_ne_three {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    Nat.card (Outer (SL(2, ZMod p))) ∣ 2 := by
  classical
  rcases hp.eq_two_or_odd' with rfl | hpodd
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcenter : Subgroup.center (SL(2, ZMod 2)) = ⊥ := by
      rw [eq_bot_iff]
      intro A hA
      rcases (CFSG.PSL2Table.mem_center_SL_iff A).mp hA with h1 | hneg
      · rw [h1]
        exact Subgroup.mem_bot.mpr rfl
      · rw [hneg]
        have hone : (-1 : SL(2, ZMod 2)) = 1 := by
          ext i j
          fin_cases i <;> fin_cases j <;> decide
        rw [hone]
        exact Subgroup.mem_bot.mpr rfl
    have ePSL : SL(2, ZMod 2) ≃* PSL(2, ZMod 2) :=
      ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
    have hcard : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod, pow_one]
    have h := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
      (p := 2) (f := 1) Nat.prime_two (ZMod 2) hcard).2 (SL(2, ZMod 2)) ⟨ePSL⟩
    have h1 : Nat.card (Outer (SL(2, ZMod 2))) ∣ 1 := by
      simpa using h
    exact h1.trans (by norm_num)
  ·
    haveI : Fact p.Prime := ⟨hp⟩
    have hp5 : 5 ≤ p := by
      have hp2 : p ≠ 2 := by
        rintro rfl
        norm_num at hpodd
      have hp4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      have hp2le : 2 ≤ p := hp.two_le
      omega
    have h4 : ∃ s : Finset (ZMod p), s.card = 4 := by
      haveI : NeZero p := ⟨hp.ne_zero⟩
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod p)))
        (n := 4) (by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_zmod]
          omega)
      exact ⟨s, hs⟩
    haveI : Group.IsPerfect (SL(2, ZMod p)) :=
      CFSG.LinearGroups.special_linear_isPerfect (K := ZMod p) (n := 2) le_rfl (Or.inr h4)
    have houtPSL : Nat.card (Outer (PSL(2, ZMod p))) ∣ 2 := by
      have hcard : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
      have h := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
        (p := p) (f := 1) hp (ZMod p) hcard).1
      have hg : (1 * Nat.gcd 2 (p ^ 1 - 1)) ∣ 2 := by
        rw [pow_one]
        simpa using Nat.gcd_dvd_left 2 (p - 1)
      exact h.trans hg
    have hinj : Function.Injective
        (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom
          (SL(2, ZMod p))) :=
      CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective _
    exact (Subgroup.card_dvd_of_injective _ hinj).trans houtPSL

theorem card_outer_SL2_dvd_two {p : ℕ} (hp : p.Prime) :
    Nat.card (Outer (SL(2, ZMod p))) ∣ 2 := by
  rcases eq_or_ne p 3 with rfl | hp3
  ·
    have hout : Nat.card (Outer (SL(2, ZMod 3))) = 2 := by
      rw [← Subgroup.index_eq_card]
      have hinner : inner (SL(2, ZMod 3)) = CFSG.ClassicalInvolution.Q3.Q3T6.inn3 := rfl
      rw [hinner, CFSG.ClassicalInvolution.Q3.Q3T6.inn3_index]
    rw [hout]
  · exact card_outer_SL2_dvd_two_of_ne_three hp hp3

theorem mulAut_eq_one_of_not_dvd_card {I : Type} [Group I] [Finite I] {p d : ℕ}
    (hp : p.Prime) (hd : d.Prime) (hd2 : d ≠ 2) (hnd : ¬ d ∣ Nat.card I)
    (hI : IsSLType 2 (ZMod p) I) (δ : MulAut I) (hδ : orderOf δ = d) : δ = 1 := by
  classical
  obtain ⟨e⟩ := hI
  have houtI : Nat.card (Outer I) ∣ 2 := by
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact card_outer_SL2_dvd_two hp
  let q : Outer I := QuotientGroup.mk' (inner I) δ
  have hqd : orderOf q ∣ d := by
    rw [← hδ]
    exact orderOf_map_dvd (QuotientGroup.mk' (inner I)) δ
  have hq2 : orderOf q ∣ 2 := (orderOf_dvd_natCard q).trans houtI
  have hq1 : orderOf q = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hq2 with h1 | h2
    · exact h1
    · exfalso
      have h2d : 2 ∣ d := by rw [h2] at hqd; exact hqd
      have h2eq : 2 = d := ((Nat.dvd_prime hd).mp h2d).resolve_left (by norm_num)
      exact hd2 h2eq.symm
  have hqeq : q = 1 := orderOf_eq_one_iff.mp hq1
  have hδinner : δ ∈ inner I := (QuotientGroup.eq_one_iff δ).mp hqeq
  obtain ⟨g, hg⟩ := hδinner
  have hdvdI : d ∣ Nat.card I := by
    calc d = orderOf (MulAut.conj g) := by rw [hg, hδ]
      _ ∣ orderOf g := orderOf_map_dvd (MulAut.conj : I →* MulAut I) g
      _ ∣ Nat.card I := orderOf_dvd_natCard g
  exact (hnd hdvdI).elim

end CFSG.LocalAnalysis.AGL81I.Section3
