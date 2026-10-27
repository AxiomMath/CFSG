module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.ComponentClassification.OuterAutomorphisms

theorem noIrrFFOffender_transfer {Y Y' : Type} [Group Y] [Group Y'] (h : NoIrrFFOffender Y)
    (f : Nonempty (Y ≃* Y')) : NoIrrFFOffender Y' := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel hquad
  obtain ⟨f⟩ := f
  exact h W hW L E hq hirr ⟨e.trans f.symm⟩ hE hEne hEel hquad

theorem card_le_two_mul_inf_inner_of_index {Y : Type} [Group Y] (hidx : (inner Y).index = 2)
    (B : Subgroup (MulAut Y)) :
    Nat.card B ≤ 2 * Nat.card ↥(B ⊓ (MulAut.conj : Y →* MulAut Y).range) := by
  have h1 := Subgroup.relIndex_mul_card (H := inner Y) (K := B)
  have h2 : (inner Y).relIndex B ≤ 2 := by
    have := Subgroup.relIndex_dvd_index_of_normal (H := inner Y) (K := B)
    rw [hidx] at this
    exact Nat.le_of_dvd (by norm_num) this
  have h3 : B ⊓ (MulAut.conj : Y →* MulAut Y).range = inner Y ⊓ B := inf_comm _ _
  rw [h3]
  calc Nat.card B = (inner Y).relIndex B * Nat.card ↥(inner Y ⊓ B) := h1.symm
    _ ≤ 2 * Nat.card ↥(inner Y ⊓ B) := Nat.mul_le_mul_right _ h2

theorem card_le_mul_card_inf_inner_of_index_dvd {Y : Type} [Group Y] {k : ℕ} (hk : 0 < k)
    (hidx : (inner Y).index ∣ k) (B : Subgroup (MulAut Y)) :
    Nat.card B ≤ k * Nat.card ↥(B ⊓ (MulAut.conj : Y →* MulAut Y).range) := by
  have h1 := Subgroup.relIndex_mul_card (H := inner Y) (K := B)
  have h2 : (inner Y).relIndex B ≤ k :=
    Nat.le_of_dvd hk ((Subgroup.relIndex_dvd_index_of_normal (H := inner Y) (K := B)).trans hidx)
  have h3 : B ⊓ (MulAut.conj : Y →* MulAut Y).range = inner Y ⊓ B := inf_comm _ _
  rw [h3]
  calc Nat.card B = (inner Y).relIndex B * Nat.card ↥(inner Y ⊓ B) := h1.symm
    _ ≤ k * Nat.card ↥(inner Y ⊓ B) := Nat.mul_le_mul_right _ h2

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
