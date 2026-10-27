module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.Minimal
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1316

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

open Subgroup
open CFSG.GH74.GLS.Bg (kLowInfty)

theorem controlsTransfer {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∀ (G : Type) [Group G] [Finite G], ControlsTransfer p G := by
  suffices h : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → ControlsTransfer p G from
    fun G _ _ => h _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn S
  have hind : ∀ H T : Subgroup G, H ≠ ⊤ → IsSylowOf p H T →
      T ⊓ ⁅H, H⁆ ≤ ⁅H ⊓ nK T, H ⊓ nK T⁆ := by
    intro H T hH hT
    have hcard : Nat.card H < n := by
      rw [← hn, ← Subgroup.card_top (G := G)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hH)
    exact (ih _ hcard ↥H rfl).sub hT
  by_cases hO : ∃ Q : Subgroup G, IsPGroup p Q ∧ Q ≠ ⊥ ∧ Q.Normal
  ·
    obtain ⟨Q, hQp, hQ1, hQn⟩ := hO
    haveI hPn : (CFSG.pCore p G).Normal := CFSG.pCore_normal
    have hPp : IsPGroup p (CFSG.pCore p G) := CFSG.pCore_isPGroup
    have hPmax : ∀ N : Subgroup G, N.Normal → IsPGroup p N → N ≤ CFSG.pCore p G :=
      fun N hN hNp => le_sSup ⟨hN, hNp⟩
    have hP1 : CFSG.pCore p G ≠ ⊥ := fun h => hQ1 (le_bot_iff.mp (h ▸ hPmax Q hQn hQp))
    have hcardq : Nat.card (G ⧸ CFSG.pCore p G) < n := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore p G)
      have h2 : 1 < Nat.card (CFSG.pCore p G) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hP1
      have h3 : 0 < Nat.card (G ⧸ CFSG.pCore p G) := Nat.card_pos
      rw [← hn, h1]
      exact lt_mul_of_one_lt_right h3 h2
    exact le_of_normal_pSubgroup hp5 S (CFSG.pCore p G) hPp hPmax hind
      (ih _ hcardq (G ⧸ CFSG.pCore p G) rfl)
  ·
    push Not at hO
    refine le_of_no_normal_pSubgroup S (fun Q hQp hQ1 hQtop => ?_) hind
    exact hO Q hQp hQ1 (normalizer_eq_top_iff.mp hQtop)

theorem glaubermanTransferControl_holds : Claims1316.GlaubermanTransferControl := by
  intro G _ _ p hp hp5 S hS
  haveI : Fact p.Prime := ⟨hp⟩
  let S' : Sylow p G :=
    { toSubgroup := S
      isPGroup' := hS.2.1
      is_maximal' := fun hQ hle => hS.2.2 _ le_top hQ hle }
  have h := controlsTransfer hp5 G S'
  rw [map_subtype_commutator]
  refine le_antisymm (le_inf inf_le_left h) (inf_le_inf_left _ ?_)
  exact Subgroup.commutator_mono le_top le_top

theorem glaubermanTransfer_holds : Claims1316.GlaubermanTransfer :=
  Claims1316.glaubermanTransfer_of_control glaubermanTransferControl_holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

end
