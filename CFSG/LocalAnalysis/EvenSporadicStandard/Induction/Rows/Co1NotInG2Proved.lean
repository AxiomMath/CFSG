module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Hyp31C
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1OrdSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G2TwoElements
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley

theorem co1NotInG2_proved
    : Co1NotInG2 := by
  intro n hn N _ hm L hL
  obtain ⟨e⟩ := hL
  obtain ⟨g, hg⟩ := Co1Ord.exists_orderOf_sixteen
  obtain ⟨-, hM⟩ := CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hm
    (by decide)
  obtain ⟨-, K, _, _, hK, ⟨f⟩⟩ := hM
  have : CharP K 2 :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.charP_two_of_card (by omega) hK rfl
  let eC : AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  let ψ : ↥L →* ↥(adjointGroup .G2 K) := (f.trans eC).toMonoidHom.comp L.subtype
  have hψ : Function.Injective ψ := (f.trans eC).injective.comp Subtype.val_injective
  let y : ↥(adjointGroup .G2 K) := ψ (e.symm g)
  have hg' : orderOf (e.symm g) = 16 := by
    have := orderOf_injective e.symm.toMonoidHom e.symm.injective g
    exact this.trans hg
  have hy : orderOf y = 16 := by
    rw [← hg']
    exact orderOf_injective ψ hψ (e.symm g)
  have h16 : (y : ModGL .G2 K) ^ 2 ^ 4 = 1 := by
    have : y ^ 16 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    exact congrArg Subtype.val this
  have h8 : y ^ 8 = 1 := Subtype.ext (pow_eight_of_two_power_g2 y.2 h16)
  have := orderOf_dvd_of_pow_eq_one h8
  rw [hy] at this
  omega

end CFSG.EvenSporadicStandard.Induction
