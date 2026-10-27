module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACtxSteps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4A

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

private theorem relIndex_ne_zero_of_finite (A B : Subgroup G) : A.relIndex B ≠ 0 := fun h0 => by
  have h := Subgroup.relIndex_dvd_card (H := A) (K := B)
  rw [h0, zero_dvd_iff] at h
  exact Nat.card_pos.ne' h

theorem relIndex_two_of_ne (h : Ctx0 t L S x₁ x₂ lam rho) (h1 : Lemma4_1Concl t L) :
    (twoCore t ⊔ L).relIndex (invCent t) = 2 := by
  have hKH : twoCore t ⊔ L ≤ invCent t := sup_le (twoCore_le_invCent t) (L_le_invCent h.hyp)
  have hle : (twoCore t ⊔ L).relIndex (invCent t) ≤ 2 := h.hyp.relIndex_le
  have hne1 : (twoCore t ⊔ L).relIndex (invCent t) ≠ 1 := fun h1' =>
    h1 (le_antisymm (Subgroup.relIndex_eq_one.mp h1') hKH)
  have hne0 : (twoCore t ⊔ L).relIndex (invCent t) ≠ 0 := relIndex_ne_zero_of_finite _ _
  omega

theorem relIndex_PT_two (h : Ctx0 t L S x₁ x₂ lam rho) (h1 : Lemma4_1Concl t L) :
    (twoCore t ⊔ wreathGrp x₁ x₂ lam).relIndex S = 2 := by
  have hK := relIndex_two_of_ne h h1
  have hKH : twoCore t ⊔ L ≤ invCent t := sup_le (twoCore_le_invCent t) (L_le_invCent h.hyp)
  rw [← h.inf_PL, Subgroup.inf_relIndex_left]
  have hle : (twoCore t ⊔ L).relIndex S ≤ (twoCore t ⊔ L).relIndex (invCent t) :=
    Subgroup.relIndex_le_of_le_right h.le_invCent (by rw [hK]; norm_num)
  have hne1 : (twoCore t ⊔ L).relIndex S ≠ 1 := by
    intro h1'
    have hSK : S ≤ twoCore t ⊔ L := Subgroup.relIndex_eq_one.mp h1'
    have hmul := Subgroup.relIndex_mul_relIndex S (twoCore t ⊔ L) (invCent t) hSK hKH
    apply h.relIndex_odd
    rw [← hmul, hK]
    exact Dvd.intro_left _ rfl
  have hne0 : (twoCore t ⊔ L).relIndex S ≠ 0 := relIndex_ne_zero_of_finite _ _
  omega

theorem card_S_of_ne (h : Ctx0 t L S x₁ x₂ lam rho) (h1 : Lemma4_1Concl t L) :
    Nat.card S = 2 ^ 6 * Nat.card (twoCore t) := by
  have hidx := relIndex_PT_two h h1
  have hPT_le : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ S := by
    rw [← h.inf_PL]; exact inf_le_left
  have hmul := Subgroup.relIndex_mul_card (H := twoCore t ⊔ wreathGrp x₁ x₂ lam) (K := S)
  rw [inf_eq_left.mpr hPT_le, hidx] at hmul
  rw [← hmul]
  have hTL : wreathGrp x₁ x₂ lam ≤ L := by rw [← h.inf_eq]; exact inf_le_right
  have hcomm : ∀ a ∈ twoCore t, ∀ b ∈ wreathGrp x₁ x₂ lam, a * b = b * a :=
    fun a ha b hb => twoCore_commute h.hyp a ha b (hTL hb)
  have hinf : twoCore t ⊓ wreathGrp x₁ x₂ lam = ⊥ := by
    have : twoCore t ⊓ wreathGrp x₁ x₂ lam ≤ twoCore t ⊓ L := inf_le_inf_left _ hTL
    rw [h.hyp.twoCore_inf] at this
    exact le_bot_iff.mp this
  rw [card_sup_of_commute hcomm hinf, h.wreath.card_wreathGrp]
  ring

end S4A

theorem ctxIdx_holds : CtxIdxStmt :=
  fun h h1 => ⟨S4A.relIndex_two_of_ne h h1, S4A.relIndex_PT_two h h1, S4A.card_S_of_ne h h1⟩

end CFSG.OddStandard.SmallF3.HarrisU33
