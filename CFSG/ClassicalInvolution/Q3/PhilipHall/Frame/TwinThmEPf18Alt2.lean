module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.TL3T1
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEC

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.TL4
open scoped commutatorElement

section Alt2

theorem uniqueInvolution_central_of_mem {Y : Type} [Group Y] {K : Subgroup Y} {u : Y}
    (hu : IsUniqueInvolution K u) {w : Y} (hw : w ∈ K) : w * u = u * w := by
  have h1 : w * u * w⁻¹ ∈ K := K.mul_mem (K.mul_mem hw hu.mem) (K.inv_mem hw)
  have h2 : (w * u * w⁻¹) * (w * u * w⁻¹) = 1 := by
    calc (w * u * w⁻¹) * (w * u * w⁻¹) = w * (u * u) * w⁻¹ := by group
      _ = 1 := by rw [hu.sq]; group
  rcases hu.unique _ h1 h2 with h | h
  · exfalso
    apply hu.ne_one
    have : u = w⁻¹ * (w * u * w⁻¹) * w := by group
    rw [this, h]; group
  · calc w * u = w * u * w⁻¹ * w := by group
      _ = u * w := by rw [h]

theorem alt2_of_fusion {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}
    (hΩ : HypOmegaGen Δ) (htwo : ∀ L ∈ Δ, IsPGroup 2 L) {K : Subgroup Y} (hK : K ∈ Δ) {z t : Y}
    (hz : IsUniqueInvolution K z) (hzt : z * t = t * z) (hne : conjSub t K ≠ K) {x : Y}
    (hx : x * z * x⁻¹ = z * t) :
    ∃ x : Y, ∃ M' ∈ twinSet Δ (conjSub x K), M' ≠ conjSub x K ∧ ∃ R₁ R₂ : Subgroup Y,
      IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧ Commutes R₁ R₂ ∧
        ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w := by
  have hconj : ∀ g : Y, ∀ L ∈ Δ, conjSub g L ∈ Δ := fun g L hL => hΩ.conjInvariant g L hL
  have hsyl : ∀ L ∈ Δ, IsSylow2In L L := fun L hL =>
    ⟨le_rfl, htwo L hL, fun V hV _ hLV => le_antisymm hV hLV⟩
  set K'' := conjSub t K with hK''def
  have hK'' : K'' ∈ Δ := hconj t K hK
  have hzK'' : IsUniqueInvolution K'' z := by
    have := hz.conj t
    rwa [show t * z * t⁻¹ = z by rw [← hzt]; group] at this
  have hKx : conjSub x K ∈ Δ := hconj x K hK
  have hK''x : conjSub x K'' ∈ Δ := hconj x K'' hK''
  have h1 : IsUniqueInvolution (conjSub x K) (z * t) := hx ▸ hz.conj x
  have h2 : IsUniqueInvolution (conjSub x K'') (z * t) := hx ▸ hzK''.conj x
  have hne' : conjSub x K'' ≠ conjSub x K := by
    intro h
    apply hne
    have := congrArg (conjSub x⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have htw : conjSub x K'' ∈ twinSet Δ (conjSub x K) :=
    ⟨hK''x, x * z * x⁻¹, hz.conj x, hzK''.conj x⟩
  refine ⟨x, conjSub x K'', htw, hne', conjSub x K, conjSub x K'', hsyl _ hKx, hsyl _ hK''x, ?_, ?_⟩
  · intro a ha b hb
    have hco := Sec6Gen.comm_le_oddCore_of_twin hΩ hKx hK''x (Ne.symm hne') (hz.conj x)
      (hzK''.conj x)
    have h0 : ⁅a, b⁆ ∈ oddCoreOf (conjSub x K) ⊓ oddCoreOf (conjSub x K'') :=
      hco (Subgroup.commutator_mem_commutator ha hb)
    have hb0 : ⁅a, b⁆ = 1 :=
      TwinExitPf12.eq_one_of_odd_orderOf_of_pGroup (htwo _ hKx) (oddCoreOf_le_self _ h0.1)
        (TwinExitPf12.odd_orderOf_of_mem_odd (odd_natCard_oddCoreOf _) h0.1)
    rw [commutatorElement_def] at hb0
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hb0, one_mul]
  · intro w hw
    have hle : conjSub x K ⊔ conjSub x K'' ≤ Subgroup.centralizer ({z * t} : Set Y) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (uniqueInvolution_central_of_mem h1 hw)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (uniqueInvolution_central_of_mem h2 hw)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

end Alt2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
