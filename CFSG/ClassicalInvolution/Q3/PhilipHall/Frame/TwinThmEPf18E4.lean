module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Base
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift
public import CFSG.ClassicalInvolution.Uniform.U5Comp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitE4
open scoped commutatorElement

section E4

theorem alt2_of_twin_centralizes {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}
    (hΩ : HypOmegaGen Δ) (htwo : ∀ L ∈ Δ, IsPGroup 2 L) {K K' : Subgroup Y} (hK : K ∈ Δ) {z : Y}
    (hz : IsUniqueInvolution K z) (hK'tw : K' ∈ twinSet Δ K) (hK'ne : K' ≠ K) (t : Y) {x : Y}
    (hx : ∀ w ∈ conjSub x K ⊔ conjSub x K', w * (z * t) = (z * t) * w) :
    ∃ x : Y, ∃ M' ∈ twinSet Δ (conjSub x K), M' ≠ conjSub x K ∧ ∃ R₁ R₂ : Subgroup Y,
      IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧ Commutes R₁ R₂ ∧
        ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w := by
  have hconj : ∀ g : Y, ∀ L ∈ Δ, conjSub g L ∈ Δ := fun g L hL => hΩ.conjInvariant g L hL
  have hsyl : ∀ L ∈ Δ, IsSylow2In L L := fun L hL =>
    ⟨le_rfl, htwo L hL, fun V hV _ hLV => le_antisymm hV hLV⟩
  obtain ⟨hK'Δ, w, hwK, hwK'⟩ := hK'tw
  have hwz : w = z := (hz.eq hwK).symm
  subst hwz
  have hKx : conjSub x K ∈ Δ := hconj x K hK
  have hK'x : conjSub x K' ∈ Δ := hconj x K' hK'Δ
  have hne' : conjSub x K' ≠ conjSub x K := by
    intro h
    apply hK'ne
    have := congrArg (conjSub x⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have htw : conjSub x K' ∈ twinSet Δ (conjSub x K) :=
    ⟨hK'x, x * w * x⁻¹, hz.conj x, hwK'.conj x⟩
  refine ⟨x, conjSub x K', htw, hne', conjSub x K, conjSub x K', hsyl _ hKx, hsyl _ hK'x, ?_, hx⟩
  intro a ha b hb
  have hco := Sec6Gen.comm_le_oddCore_of_twin hΩ hKx hK'x (Ne.symm hne') (hz.conj x)
    (hwK'.conj x)
  have h0 : ⁅a, b⁆ ∈ oddCoreOf (conjSub x K) ⊓ oddCoreOf (conjSub x K') :=
    hco (Subgroup.commutator_mem_commutator ha hb)
  have hb0 : ⁅a, b⁆ = 1 :=
    TwinExitPf12.eq_one_of_odd_orderOf_of_pGroup (htwo _ hKx) (oddCoreOf_le_self _ h0.1)
      (TwinExitPf12.odd_orderOf_of_mem_odd (odd_natCard_oddCoreOf _) h0.1)
  rw [commutatorElement_def] at hb0
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [hb0, one_mul]

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

end E4

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
