module

public import CFSG.GH74.Generic.S1.UniDiag

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.Generic.S1.Uni

theorem exists_unitaryFieldData {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) :
    ∃ p f : ℕ, UnitaryFieldData p f F ∧ q = p ^ f ∧ p ≠ 2 := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  have hp2 : p ≠ 2 := prime_ne_two_of_odd_card (F := F) (p := p) hodd
  have hf : 1 ≤ f := by
    by_contra hf0
    have hf0' : f = 0 := by omega
    subst hf0'
    simp at hF
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  exact ⟨p, f, ⟨hp.out, hf, by rw [hF, ← pow_mul, mul_comm]⟩, rfl, hp2⟩

theorem classify_uni {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) (α : MulAut ↥(StatedSU 4 q F)) (hα : α * α = 1)
    (hout : ∀ k : ↥(StatedSU 4 q F), α ≠ MulAut.conj k) :
    GoodFixedCentral False α ∨ IsReflection (StatedSU 4 q F) α ∨
      IsGraphFieldLike (StatedSU 4 q F) q α := by
  obtain ⟨p, f, h, rfl, hp2⟩ := exists_unitaryFieldData hF hq
  have hα1 : α ≠ 1 := fun h1 => hout 1 (by rw [h1, map_one])
  obtain ⟨A, σ, hσ, hAu, hαA, hid, hbar⟩ := aut_form_uni h hp2 α hα hα1
  rcases hσ with rfl | hσb
  · obtain ⟨c, hc0, hAA⟩ := hid rfl
    have := classify_diag h hp2 hq α hout hAu
      (fun k => by rw [hαA k, glAut_refl_apply]) hc0 hAA
    rcases this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · obtain ⟨c, hc0, hAA⟩ := hbar hσb
    refine Or.inr (Or.inr ⟨h.bar, A, fun x => h.bar_apply x, ⟨c, hAA⟩, fun k => ?_⟩)
    rw [hαA k]
    congr 2
    apply Units.ext
    ext i j
    simp [coe_glAut, hσb]

end CFSG.GH74.Generic.S1
