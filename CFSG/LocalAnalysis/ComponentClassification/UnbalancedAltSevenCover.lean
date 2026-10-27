module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenLift
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenQuaternion

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedAltSeven

open Equiv Subgroup CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier

theorem altSevenPi_surjective : Function.Surjective altSevenPi := by
  intro σ
  obtain ⟨g, hg⟩ := lyPi_surjective (altExtend σ)
  have hgE : g ∈ altSevenE := by
    change lyPi g ∈ stabFour
    rw [hg]
    exact altExtend_mem_stabFour σ
  refine ⟨⟨g, hgE⟩, ?_⟩
  rw [altSevenPi_apply]
  have : (⟨lyPi g, hgE⟩ : stabFour) = ⟨altExtend σ, altExtend_mem_stabFour σ⟩ := Subtype.ext hg
  rw [this, relabel_altExtend]

theorem orderOf_altSevenZ : orderOf altSevenZ = 2 := by
  rw [← Subgroup.orderOf_coe, show ((altSevenZ : lyC)) = zC from rfl, orderOf_zC]

theorem altSevenZ_mem_center : altSevenZ ∈ center altSevenE :=
  mem_center_iff.2 fun g => Subtype.ext (mem_center_iff.1 zC_mem_center g)

theorem altSevenPi_ker : altSevenPi.ker = zpowers altSevenZ := by
  ext g
  rw [MonoidHom.mem_ker, mem_zpowers_of_orderOf_eq_two orderOf_altSevenZ, altSevenPi_apply,
    MulEquiv.map_eq_one_iff]
  have h1 : ((⟨lyPi g, g.2⟩ : stabFour) = 1) ↔ (g : lyC) ∈ zGroup := by
    rw [← lyPi_ker, MonoidHom.mem_ker, ← Subtype.val_inj]
    rfl
  rw [h1, mem_zGroup]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem lyPi_cStar_eight : lyPi ⟨cStar 8, cStar_mem 8⟩ = altExtend tZero := by
  apply Subtype.ext
  rw [coe_lyPi, imgC_cStar (by norm_num), coe_altExtend_tZero,
    ly_double_transposition_lift_square.2.1]

theorem cStar_eight_mem_altSevenE : (⟨cStar 8, cStar_mem 8⟩ : lyC) ∈ altSevenE := by
  change lyPi _ ∈ stabFour
  rw [lyPi_cStar_eight]
  exact altExtend_mem_stabFour tZero

@[expose] def altSevenX : altSevenE := ⟨⟨cStar 8, cStar_mem 8⟩, cStar_eight_mem_altSevenE⟩

theorem altSevenX_sq : altSevenX ^ 2 = altSevenZ :=
  Subtype.ext (Subtype.ext ly_double_transposition_lift_square.1)

theorem altSevenPi_altSevenX : altSevenPi altSevenX = tZero := by
  rw [altSevenPi_apply]
  have : (⟨lyPi altSevenX, altSevenX.2⟩ : stabFour) =
      ⟨altExtend tZero, altExtend_mem_stabFour tZero⟩ := Subtype.ext lyPi_cStar_eight
  rw [this, relabel_altExtend]

theorem alternating_seven_cover_quasisimple_quaternion :
    Function.Surjective altSevenPi ∧ altSevenPi.ker = zpowers altSevenZ ∧
      orderOf altSevenZ = 2 ∧ Nat.card altSevenE = 5040 ∧ Group.IsPerfect altSevenE ∧
      center altSevenE = zpowers altSevenZ ∧
      Nonempty (altSevenE ⧸ center altSevenE ≃* alternatingGroup (Fin 7)) ∧
      (∀ y : altSevenE, orderOf y = 2 → y = altSevenZ) ∧
      ∀ S : Sylow 2 altSevenE, Nonempty (S ≃* QuaternionGroup 4) ∧ Nat.card S = 16 := by
  obtain ⟨hcard, hperf, hcen, hquot, huniq, hsyl⟩ :=
    cover_of_lift altSevenZ_mem_center orderOf_altSevenZ altSevenPi_surjective altSevenPi_ker
      altSevenX_sq altSevenPi_altSevenX
  exact ⟨altSevenPi_surjective, altSevenPi_ker, orderOf_altSevenZ, hcard, hperf, hcen, hquot,
    huniq, hsyl⟩

end CFSG.ComponentClassification.UnbalancedAltSeven
