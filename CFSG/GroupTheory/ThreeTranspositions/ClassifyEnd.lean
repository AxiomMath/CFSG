module

public import CFSG.GroupTheory.ThreeTranspositions.Basic
public import CFSG.Blueprint.FischerDefs
import CFSG.Fischer.Classification.Symplectic.Recognition
import CFSG.Fischer.Classification.Basic.Transitivity
import CFSG.GroupTheory.ThreeTranspositions.SymplecticType
import CFSG.GroupTheory.ThreeTranspositions.ConfigE9
import CFSG.GroupTheory.ThreeTranspositions.SymEnd

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Symplectic

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {X : Type} [Group X] {E : Set X}

private theorem hasE9_of_hasOrthHypPairs (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup ↥(commutator X)) (hsymp : IsSymplecticType E)
    (htrans : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ e ∈ E, a ≠ b → a * b = b * a → c ≠ e →
      c * e = e * c → ∃ g : X, g * a * g⁻¹ = c ∧ g * b * g⁻¹ = e)
    (h : HasOrthHypPairs (sympConfig hP hZ hS hsymp htrans)) : HasE9 X := by
  obtain ⟨d, ⟨d₀, rfl⟩, e, ⟨e₀, rfl⟩, u, ⟨u₀, rfl⟩, w, ⟨w₀, rfl⟩, hde, huw, hdu, hdw, heu,
    hew⟩ := h
  have hde' : ncomm (d₀ : X) e₀ = 1 := by rw [← sympForm_bar]; exact hde
  have huw' : ncomm (u₀ : X) w₀ = 1 := by rw [← sympForm_bar]; exact huw
  have hdu' : ncomm (d₀ : X) u₀ = 0 := by rw [← sympForm_bar]; exact hdu
  have hdw' : ncomm (d₀ : X) w₀ = 0 := by rw [← sympForm_bar]; exact hdw
  have heu' : ncomm (e₀ : X) u₀ = 0 := by rw [← sympForm_bar]; exact heu
  have hew' : ncomm (e₀ : X) w₀ = 0 := by rw [← sympForm_bar]; exact hew
  rw [ncomm_eq_one_iff] at hde' huw'
  rw [ncomm_eq_zero_iff] at hdu' hdw' heu' hew'
  have hsq : ∀ x : E, (x : X) ^ 2 = 1 := fun x => by rw [sq]; exact Pair.mul_self hP x.2
  have hcube : ∀ x y : E, (x : X) * y ≠ y * x → ((x : X) * y) ^ 3 = 1 := fun x y hxy => by
    rw [← Pair.orderOf_mul_eq_three hP x.2 y.2 hxy]; exact pow_orderOf_eq_one _
  exact hasE9_of_commuting_pairs (hsq d₀) (hsq e₀) (hsq u₀) (hsq w₀) (hcube d₀ e₀ hde')
    (hcube u₀ w₀ huw') hde' huw' hdu' hdw' heu' hew'

theorem card_eq_six_or_one_twenty_of_pair (hP : Pair X E) (hX : ¬ HasE9 X)
    (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup ↥(commutator X)) :
    Nat.card X = 6 ∨ Nat.card X = 120 := by
  have hsymp : IsSymplecticType E := isSymplecticType_of_not_hasE9 hP hX
  have htrans : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ e ∈ E, a ≠ b → a * b = b * a → c ≠ e →
      c * e = e * c → ∃ g : X, g * a * g⁻¹ = c ∧ g * b * g⁻¹ = e :=
    fun a ha b hb c hc e he hab habc hce hcec =>
      Pair.exists_conj_pair_of_commute hP hZ hS ha hb hc he hab habc hce hcec
  haveI := Pair.finite hP
  rcases tn_or_hasOrthHypPairs (sympConfig hP hZ hS hsymp htrans) with hTN | hOrth
  · obtain ⟨m, hm, φ, -⟩ := classicalConclusion_sym hP hZ hS hsymp htrans hTN
    exact card_eq_six_or_one_twenty_of_mulEquiv_perm hm φ hX
  · exact absurd (hasE9_of_hasOrthHypPairs hP hZ hS hsymp htrans hOrth) hX

end CFSG.GroupTheory.ThreeTranspositions
