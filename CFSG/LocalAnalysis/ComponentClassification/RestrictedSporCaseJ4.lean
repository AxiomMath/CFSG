module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs
public import CFSG.Sporadic.Schreier.J4SOutOdd

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem mem_inner_of_odd_card_outer {G : Type*} [Group G]
    (hodd : Odd (Nat.card (Outer G))) {α : MulAut G} (h2 : α * α = 1) : α ∈ inner G := by
  have hdvd : orderOf (α : Outer G) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [sq, ← QuotientGroup.mk_mul, h2, QuotientGroup.mk_one]
  have hodd' : ¬ 2 ∣ Nat.card (Outer G) := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.2 hodd
  have h1 : orderOf (α : Outer G) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · exact absurd (h ▸ orderOf_dvd_natCard (α : Outer G)) hodd'
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem sporadicCase_J4_of_inputs (hin : J4NoComponentsInput) : SporadicCase .J4 := by
  refine sporadicCase_of_comps (fun G _ _ hG t ht B hB => absurd hB (hin G hG t ht B))
    (fun G _ _ _ _ ⟨e⟩ α hα2 hα => ?_)
  exfalso
  have eJ : G ≃* Sporadic.J4.J := e.trans (Sporadic.J4.seedEquiv Sporadic.J4.j4Facts.mat)
  have hcard : Nat.card (Outer G) = Nat.card (Outer Sporadic.J4.J) := by
    have h := @Sporadic.J4Schreier.card_outer_congr G Sporadic.J4.J _
      (Subgroup.toGroup Sporadic.J4.J) eJ
    exact h
  have hodd : Odd (Nat.card (Outer G)) := by
    rw [hcard]
    exact Sporadic.J4Schreier.CTU_J4_outer_automorphism_group_odd_order
  exact hα (mem_inner_of_odd_card_outer hodd hα2)

end CFSG.ComponentClassification.RestrictedStd.Spor
