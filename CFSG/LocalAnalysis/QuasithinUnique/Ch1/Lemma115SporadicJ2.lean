module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.J2Cover

theorem j2_outer_fixSub_card
    (α : MulAut P) (hα2 : α * α = 1) (hα : α ∉ inner P) :
    Nat.card (fixSub α) ∈ ({336} : Set ℕ) := by
  refine outer_fixSub_card P permU permU_conj_mem (by rw [permU_mul_self]; exact P.one_mem)
    center_P permU_outer (by rw [card_mulAut_P, card_P]) (fun u hu ho => ?_) α hα2 hα
  obtain ⟨c, hc, rfl⟩ := outer_classes.1 u hu ho
  rw [Set.mem_singleton_iff, centralizerIn_conj _ hc, outer_classes.2.2,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact centOuter_facts.2.1

theorem j2AutInner
    (K : Type) [Group K] [Finite K] (hK : Nonempty (K ≃* NativeSporadic.J2))
    (β : K ≃* K) (hβ : ∀ x, β (β x) = x)
    (hP : ∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) : IsInnerAut β := by
  obtain ⟨e⟩ := hK
  refine autInner_of_equiv_of_outer_card (e.trans nativeEquivP) (m := 604800)
    (by rw [Nat.card_congr (e.trans nativeEquivP).toEquiv, card_P]) (S := {336}) ?_
    (fun α hα2 hα => j2_outer_fixSub_card α hα2 hα) β hβ hP
  intro c hc k i hk hki
  rw [Set.mem_singleton_iff] at hc
  subst hc
  have hk4 : k ≤ 4 := by
    by_contra h
    have h5 : 2 ^ 5 ∣ 336 := dvd_trans (pow_dvd_pow 2 (by omega)) hk
    omega
  interval_cases k <;> omega

@[expose] def IsSporadicRestName (s : TauCeti.SporadicName) : Prop :=
  s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru

@[expose] def SporadicRestAutInner : Prop :=
  ∀ (s : TauCeti.SporadicName), IsSporadicRestName s → ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* NativeSporadic.Carrier s) → ∀ β : K ≃* K, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) → IsInnerAut β

theorem sporadicResidualAutInner_of_rest
    (h : SporadicRestAutInner) :
    SporadicResidualAutInner := by
  intro s hs K _ _ hK β hβ hP
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact j2AutInner K hK β hβ hP
  · exact h .J4 (Or.inl rfl) K hK β hβ hP
  · exact h .HS (Or.inr (Or.inl rfl)) K hK β hβ hP
  · exact h .He (Or.inr (Or.inr (Or.inl rfl))) K hK β hβ hP
  · exact h .Ru (Or.inr (Or.inr (Or.inr rfl))) K hK β hβ hP

end CFSG.QuasithinUnique.Ch1
