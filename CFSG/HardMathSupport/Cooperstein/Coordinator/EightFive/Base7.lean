module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7Irr
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7Nat
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7Four
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Bookkeeping
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Perfect

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.QuasithinUnique Equiv Equiv.Perm

theorem tperm_seven : TPerm 7 := by
  intro V _ _ hV H ψ hψ hA hP
  obtain ⟨A, hAoff⟩ := hP
  set L := altPre ψ with hLdef
  have hq : ∀ Y₀ Y₁ : Subgroup V, IsChiefFac H Y₀ Y₁ → ¬ IsCentralSec L Y₀ Y₁ →
      (1 : WithTop ℚ) ≤ qOf (autSec H Y₁ Y₀) := by
    intro Y₀ Y₁ hY hYL
    obtain ⟨A₀, -, hA₀, -⟩ := exists_isFFStarOffender_autSec_of_offender (by norm_num) hψ hA
      hY.stab₀ hY.stab₁ hY.le hYL hAoff
    exact (qOf_autSec_eq_one hV hψ hA hY.le hY.stab₀ hY.stab₁ hYL
      (irr_of_isChiefFac hV hψ hA hAoff hY hYL) hA₀) ▸ le_rfl
  have hone := oneNoncentral_of_one_le_qOf hV (by norm_num) hψ hA ⟨A, hAoff⟩ hq
  have hVL : commV L ≠ ⊥ := by
    intro h
    obtain ⟨σ, hσ⟩ := exists_isThreeCycle (m := 7) (by norm_num)
    set l : ↥L := (altPreEquiv hψ hA).symm σ with hl
    have hl1 : (l : MulAut V) ≠ 1 := by
      intro h1
      have h2 : l = 1 := Subtype.ext h1
      have h3 : σ = 1 := by
        rw [← (altPreEquiv hψ hA).apply_symm_apply σ, ← hl, h2, map_one]
      exact hσ.ne_one (congrArg Subtype.val h3)
    apply hl1
    ext v
    have hmem : (l : MulAut V) v * v⁻¹ ∈ commV L := mul_inv_mem_commV l.2 v
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  obtain ⟨hU, hUL, -, -⟩ := u1_altPre (by norm_num) hψ hA hVL hone
  obtain ⟨A₀, -, hA₀, -⟩ := exists_isFFStarOffender_autSec_of_offender (by norm_num) hψ hA
    hU.stab₀ hU.stab₁ hU.le hUL hAoff
  have C := ctx_autSec (Or.inr rfl) hψ hA hU.stab₀ hU.stab₁ hUL
  have hI := isIrrSec_autSec (altPre_le.trans hU.stab₀) (altPre_le.trans hU.stab₁) hU.lt
    (irr_of_isChiefFac hV hψ hA hAoff hU hUL)
  rcases asB42Alt7_ctx (sq_eq_one_sec hV _ _) C hI hA₀ with h5 | h7
  ·
    left
    exact (natVia_commV_of_isAltNaturalSection (by norm_num) hψ hA
      (isAltNaturalSection_of_case5 hψ hA hU.stab₀ hU.stab₁ hUL hA₀ h5)).2
  ·
    right
    left
    obtain ⟨hGJ, hJL, -, hcard16, -, -⟩ := h7
    have hcH := card_autSec_eq_card (by norm_num) hψ hA hU.stab₀ hU.stab₁ hUL (le_refl H)
    have hcL := card_autSec_eq_card (by norm_num) hψ hA hU.stab₀ hU.stab₁ hUL
      (altPre_le (ψ := ψ))
    have hHL : L = H := Subgroup.eq_of_le_of_card_ge altPre_le (by
      rw [← hcH, ← hcL, hGJ.trans hJL])
    refine ⟨rfl, le_antisymm ?_ hA, ?_⟩
    · rintro _ ⟨h, rfl⟩
      have hh : (h : MulAut V) ∈ L := by
        rw [hHL]
        exact h.2
      exact coe_mem_altPre_iff.1 hh
    · have hcomm : commV H = commV L := congrArg commV hHL.symm
      rw [hcomm]
      refine card_commV_of_relIndex hV ⟨altPreEquiv hψ hA⟩ ?_
      rw [Subgroup.relIndex, ← Subgroup.inf_subgroupOf_left]
      exact hcard16

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
