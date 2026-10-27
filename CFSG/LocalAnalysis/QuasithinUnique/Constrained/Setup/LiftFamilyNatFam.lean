module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyB

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ABGLocalTools
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Global

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] in
theorem conj_comm_moves {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {k : V ≃ₗ[ZMod 2] V} (hk : k ∈ L)
    (hmove : ⁅L, A⁆ ≠ ⊥) : ⁅L, conjSub k A⁆ ≠ ⊥ := by
  intro hbot
  apply hmove
  have h1 : ⁅L, conjSub k A⁆ = conjSub k ⁅L, A⁆ := by
    have : conjSub k L = L := conjSub_eq_self (Subgroup.le_normalizer hk)
    conv_lhs => rw [← this]
    show ⁅L.map (MulAut.conj k).toMonoidHom, A.map (MulAut.conj k).toMonoidHom⁆ =
      ⁅L, A⁆.map (MulAut.conj k).toMonoidHom
    rw [Subgroup.map_commutator]
  rw [h1] at hbot
  exact (conjSub k).injective (hbot.trans (conjSub k).map_bot.symm)

theorem global_alt (ctx : FamilyCtx H T n F r Lc) :
    (∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → A ≤ Lc i) ∨
      (∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → ¬ A ≤ Lc i) := by
  by_cases h : ∃ i₀ A₀, IsMinOffender H A₀ ∧ ⁅Lc i₀, A₀⁆ ≠ ⊥ ∧ A₀ ≤ Lc i₀
  · left
    obtain ⟨i₀, A₀, hA₀, hmove₀, hle₀⟩ := h
    intro i A hA hmove
    obtain ⟨t, ht, hconj, -, -⟩ := family_trans ctx i₀ i
    have htH : t ∈ H := T_le_H ctx ht
    have hconj' : conjSub t (Lc i₀) = Lc i := hconj
    have hA₁ : IsMinOffender H (conjSub t A₀) := hA₀.conj htH
    have hmove₁ : ⁅Lc i, conjSub t A₀⁆ ≠ ⊥ := by
      intro hbot
      apply hmove₀
      have h1 : ⁅Lc i, conjSub t A₀⁆ = conjSub t ⁅Lc i₀, A₀⁆ := by
        rw [← hconj']
        show ⁅(Lc i₀).map (MulAut.conj t).toMonoidHom, A₀.map (MulAut.conj t).toMonoidHom⁆ =
          ⁅Lc i₀, A₀⁆.map (MulAut.conj t).toMonoidHom
        rw [Subgroup.map_commutator]
      rw [h1] at hbot
      exact (conjSub t).injective (hbot.trans (conjSub t).map_bot.symm)
    have hle₁ : conjSub t A₀ ≤ Lc i := by
      rw [← hconj']
      exact (conjSub t).monotone hle₀
    have hN₁ : NatData (Lc i) (conjSub t A₀) (ctx.α i) := by
      rcases alt_dichotomy ctx hA₁ i hmove₁ with hN | ⟨-, -, hnle, -⟩
      · exact hN
      · exact absurd hle₁ hnle
    rcases alt_dichotomy ctx hA i hmove with ⟨hAL, -⟩ | hD
    · exact hAL
    · exact (not_natData_and_delData ctx.hF (ctx.α i) hN₁ hD).elim
  · right
    push Not at h
    intro i A hA hmove hle
    exact h i A hA hmove hle

end Global

end CFSG.QuasithinUnique.Setup.Lift
