module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutRu

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def J4AutInner : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* NativeSporadic.Carrier .J4) → ∀ β : K ≃* K,
    (∀ x, β (β x) = x) → (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) → IsInnerAut β

@[expose] def J4OutOdd : Prop := Odd (Nat.card (Outer (NativeSporadic.Carrier .J4)))

theorem isInnerAut_of_outer_odd {K : Type} {N : Type*} [Group K] [Group N] (ψ : K ≃* N)
    (hodd : Odd (Nat.card (Outer N))) (β : K ≃* K) (hβ : ∀ x, β (β x) = x) : IsInnerAut β := by
  refine isInnerAut_of_transAut_mem_inner ψ β ?_
  let q : Outer N := QuotientGroup.mk (transAut ψ β)
  have h2 : q ^ 2 = 1 := by
    rw [sq, ← QuotientGroup.mk_mul]
    have : transAut ψ β * transAut ψ β = 1 := transAut_mul_self ψ β hβ
    rw [this, QuotientGroup.mk_one]
  by_contra hne
  have hne' : q ≠ 1 := fun h => hne ((QuotientGroup.eq_one_iff _).1 h)
  have hord : orderOf q = 2 := orderOf_eq_prime h2 hne'
  have hdvd : orderOf q ∣ Nat.card (Outer N) := orderOf_dvd_natCard q
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem j4AutInner_of_outOdd (h : J4OutOdd) : J4AutInner := by
  intro K _ _ hK β hβ _
  obtain ⟨e⟩ := hK
  exact isInnerAut_of_outer_odd e h β hβ

theorem sporadicRestAutInner_of_J4
    (hJ4 : J4AutInner) : SporadicRestAutInner := by
  intro s hs K _ _ hK β hβ hP
  rcases hs with rfl | rfl | rfl | rfl
  · exact hJ4 K hK β hβ hP
  · exact hsAutInner K hK β hP
  · exact heAutInner K hK β hβ hP
  · exact ruAutInner K hK β hP

theorem sporadicRestAutInner_of_J4OutOdd
    (h : J4OutOdd) : SporadicRestAutInner :=
  sporadicRestAutInner_of_J4 (j4AutInner_of_outOdd h)

theorem sporadicResidualAutInner_of_J4
    (hJ4 : J4AutInner) : SporadicResidualAutInner :=
  sporadicResidualAutInner_of_rest (sporadicRestAutInner_of_J4 hJ4)

end CFSG.QuasithinUnique.Ch1
