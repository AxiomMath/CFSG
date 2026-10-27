module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

namespace Perp23

section Inputs

@[expose] def Two23R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t → TwinPerp.TwoTwins R →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
        MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W →
          ∀ g ∈ MGrp (CoreAssembly.conjClass (tightCore R)) W, g * t * g⁻¹ ≠ t →
            Subgroup.centralizer ({g * t * g⁻¹} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤

end Inputs

section Main

theorem isPGroup_quaternion (k : ℕ) : IsPGroup 2 (QuaternionGroup (2 ^ k)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := k + 2) ?_
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  ring

theorem exists_pow_mem_oddCoreIn {Y : Type} [Group Y] {J : Subgroup Y}
    (h2 : IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)) {x : Y} (hx : x ∈ J) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ oddCoreIn J := by
  obtain ⟨k, hk⟩ := h2 (QuotientGroup.mk ⟨x, hx⟩)
  refine ⟨k, ?_⟩
  have hmem : (⟨x, hx⟩ : ↥J) ^ 2 ^ k ∈ classicalInvolutionOddCore ↥J :=
    (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow]; exact hk)
  exact ⟨_, hmem, rfl⟩

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem isPGroup_quot_of_member (h : PerpHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) :
    IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J) := by
  obtain ⟨e⟩ := h.quotEquiv hJ
  exact (isPGroup_quaternion (r - 2)).of_equiv e.symm

end Main

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
