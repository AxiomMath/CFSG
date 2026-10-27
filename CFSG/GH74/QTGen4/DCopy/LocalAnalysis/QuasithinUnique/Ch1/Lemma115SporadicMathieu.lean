module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
public import CFSG.GH74.QTGen4.DCopy.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Sporadic

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def SporadicResidualAutInner_F4 : Prop :=
  ∀ (s : TauCeti.SporadicName), IsSporadicResidualName s → ∀ (K : Type) [Group K] [CFSG.GH74.QTGen4.Finite4 K],
    Nonempty (K ≃* NativeSporadic.Carrier s) → ∀ β : K ≃* K, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) → IsInnerAut β

theorem sporadicAutInner_of_residual_F4
    (h : SporadicResidualAutInner_F4) : SporadicAutInner_F4 := by
  intro s hs hs1 K _ _ ⟨e⟩ β hβ hP
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact autInner_of_equiv_of_inner e m11_all_inner β
  ·
    let ψ : K ≃* m12D.originalSubgroup := e.trans m12EquivD
    refine autInner_of_equiv_of_outer_card ψ (m := 95040) (S := ({120} : Set ℕ)) ?_ ?_ ?_ β hβ hP
    · rw [Nat.card_congr ψ.toEquiv, ← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2]
    · intro c hc k i hk hki
      have hc' : c = 120 := by simpa using hc
      subst hc'
      have hk8 : 2 ^ k ≤ 120 := Nat.le_of_dvd (by norm_num) hk
      have hk7 : k < 7 := by
        by_contra hlt
        have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k <;> omega
    · exact m12D_outer_fixSub_card
  ·
    refine autInner_of_equiv_of_outer_card e (m := 443520) (S := ({320, 1344} : Set ℕ)) ?_ ?_ ?_
      β hβ hP
    · rw [Nat.card_congr e.toEquiv]
      exact m22_card
    · intro c hc k i hk hki
      have hc' : c = 320 ∨ c = 1344 := by simpa using hc
      have hk8 : 2 ^ k ≤ 1344 := by
        rcases hc' with rfl | rfl
        · exact (Nat.le_of_dvd (by norm_num) hk).trans (by norm_num)
        · exact Nat.le_of_dvd (by norm_num) hk
      have hk11 : k < 11 := by
        by_contra hlt
        have : 2 ^ 11 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k <;> rcases hc' with rfl | rfl <;> omega
    · intro α hα2 hα
      exact m22_outer_fixSub_card α hα2 hα
  · exact autInner_of_equiv_of_inner e m23_all_inner β
  · exact autInner_of_equiv_of_inner e m24_all_inner β
  · exact absurd rfl hs1
  · exact h _ (by simp [IsSporadicResidualName]) K ⟨e⟩ β hβ hP
  · exact h _ (by simp [IsSporadicResidualName]) K ⟨e⟩ β hβ hP
  · exact h _ (by simp [IsSporadicResidualName]) K ⟨e⟩ β hβ hP
  · exact h _ (by simp [IsSporadicResidualName]) K ⟨e⟩ β hβ hP
  · exact h _ (by simp [IsSporadicResidualName]) K ⟨e⟩ β hβ hP

end CFSG.QuasithinUnique.Ch1
