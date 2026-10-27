module

public import CFSG.ClassicalInvolution.Q3.TL3T21

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform

namespace TwinDisc

namespace ExitO2

structure Q8Fam (Y : Type) [Group Y] [Finite Y] (Δ : Set (Subgroup Y)) : Prop where
  hyp : HypOmegaGen Δ
  two : ∀ L ∈ Δ, IsPGroup 2 L
  q8 : ∀ L ∈ Δ, Nonempty (↥L ≃* QuaternionGroup 2)
  aEmpty : ∀ L ∈ Δ, AEmpty Δ L
  gen : TC.Thin.pSpan Δ = ⊤
  trans : ∀ L ∈ Δ, ∀ L' ∈ Δ, ∃ g : Y, conjSub g L = L'
  oddFree : classicalInvolutionOddCore Y = ⊥
  inO2 : ∀ L ∈ Δ, ∀ u : Y, IsUniqueInvolution L u →
    ∃ Q : Subgroup Y, Q.Normal ∧ IsPGroup 2 ↥Q ∧ u ∈ Q

section Fam

variable {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}

theorem Q8Fam.card (F : Q8Fam Y Δ) : ∀ L ∈ Δ, Nat.card ↥L = 2 ^ 3 := by
  intro L hL
  obtain ⟨e⟩ := F.q8 L hL
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  norm_num

theorem Q8Fam.pow_four (F : Q8Fam Y Δ) : ∀ L ∈ Δ, ∀ x ∈ L, x ^ 4 = 1 := by
  intro L hL x hx
  obtain ⟨e⟩ := F.q8 L hL
  have hq : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
  have h1 : (⟨x, hx⟩ : ↥L) ^ 4 = 1 := by
    have h2 := congrArg e.symm (hq (e ⟨x, hx⟩))
    rwa [map_pow, MulEquiv.symm_apply_apply, map_one] at h2
  simpa using congrArg (fun z : ↥L => (z : Y)) h1

theorem Q8Fam.exists_mul_self_ne_one (F : Q8Fam Y Δ) :
    ∀ L ∈ Δ, ∃ x ∈ L, x * x ≠ 1 := by
  intro L hL
  obtain ⟨e⟩ := F.q8 L hL
  refine ⟨((e.symm (QuaternionGroup.a 1) : ↥L) : Y), (e.symm (QuaternionGroup.a 1)).2, fun h => ?_⟩
  have h' : e.symm (QuaternionGroup.a 1 * QuaternionGroup.a 1) = 1 := by
    rw [map_mul]
    exact Subtype.ext h
  rw [MulEquiv.map_eq_one_iff] at h'
  exact absurd h' (by decide)

theorem Q8Fam.thmDConcl (F : Q8Fam Y Δ) {n : ℕ} (hD : TC.Thin.ThmDAbsBelow 3 n)
    (hn : Nat.card Y < n) : TC.Thin.ThmDConcl Δ :=
  hD Y hn Δ F.hyp F.two F.card F.aEmpty F.gen F.trans F.oddFree F.inO2

end Fam

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

end ExitO2

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
