module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcToral

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem gomi_not_pow_five_dvd {n : ℕ} (hn : Odd n) (hn1 : 1 < n) : ¬ n ^ 5 ∣ 51840 := by
  intro h
  have hle : n ^ 5 ≤ 51840 := Nat.le_of_dvd (by norm_num) h
  have hn8 : n ≤ 8 := by
    by_contra h8
    have : 9 ^ 5 ≤ n ^ 5 := Nat.pow_le_pow_left (not_le.1 h8) 5
    omega
  interval_cases n <;> first | exact absurd hn (by decide) | exact absurd h (by decide)

section Adjoint

variable {F : Type} [Field F]

theorem gomi_adjointGroup_pow_five_dvd
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    Nat.card F ^ 5 ∣ Nat.card (adjointGroup τ F) := by
  classical
  have h0 : 0 < τ.rank := τ.rank_pos
  let b : Fin τ.rank → Fˣ := fun i => if i = ⟨0, h0⟩ then -1 else 1
  have hb : ∀ i, b i = 1 ∨ b i = -1 := fun i => by
    by_cases h : i = ⟨0, h0⟩ <;> simp [b, h]
  have hne : ∃ i, b i = -1 := ⟨⟨0, h0⟩, by simp [b]⟩
  refine (gomi_toral_pow_five_dvd hτ b hb hne).trans (Subgroup.card_dvd_of_le ?_)
  unfold toralCentralizer
  exact inf_le_left

end Adjoint

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
