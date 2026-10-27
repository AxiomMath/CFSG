module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Ctx

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Asc82Basic10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec10Z G t L S z →
    IsPSp43 L ∧ t ∈ centralizer (L : Set G) ∧ t ∉ L ∧ t ∈ S ∧ S ≤ normalizer (L : Set G) ∧
      IsSylow2Of (S ⊓ L) L

private theorem isSimpleGroup_quotient_oddCore_of_psp4 [Finite G] {L : Subgroup G}
    (h : LieModel (L ⧸ oddCore L) .PSp 2 3 1) : IsSimpleGroup (L ⧸ oddCore L) := by
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)
  exact (CFSG.LieType.Simplicity.fam_classical_converse (L ⧸ oddCore L)
    ⟨.PSp, 2, 3, 1, hmodel⟩).2.2

private theorem not_mem_of_mem_centralizer_of_psp4 [Finite G] {t : G} {L : Subgroup G}
    (hq : IsQuasisimple ↥L) (h : LieModel (L ⧸ oddCore L) .PSp 2 3 1)
    (hbot : oddCore ↥L = ⊥) (ht : orderOf t = 2)
    (htc : t ∈ centralizer (L : Set G)) : t ∉ L := by
  intro htL
  have hs : IsSimpleGroup (L ⧸ oddCore L) := isSimpleGroup_quotient_oddCore_of_psp4 h
  have hcenter : Subgroup.center ↥L = oddCore ↥L := center_eq_oddCore_of_simple hq hs
  have htc' : (⟨t, htL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (htc a a.2)
  have htO : (⟨t, htL⟩ : ↥L) ∈ oddCore ↥L := hcenter ▸ htc'
  have ht1 : (⟨t, htL⟩ : ↥L) = 1 := by
    have : (⟨t, htL⟩ : ↥L) ∈ (⊥ : Subgroup ↥L) := by simpa [hbot] using htO
    simpa using this
  have hval : t = 1 := congrArg Subtype.val ht1
  rw [hval, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem asc82Basic10_of (h36 : Asc82Lemma36) (hSchur : Asc82SchurOmega5) : Asc82Basic10 := by
  intro G _ _ t L S z h
  have hq : IsQuasisimple ↥L := h.component.isQuasisimple
  have hbot : oddCore ↥L = ⊥ := hSchur ↥L hq h.psp4
  have hpsp : IsPSp43 L := by
    rw [IsPSp43]
    exact LieModel.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot) h.psp4
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer h.toSec3Setting
  have htnotL : t ∉ L :=
    not_mem_of_mem_centralizer_of_psp4 hq h.psp4 hbot h.involution htC
  have htS : t ∈ S := sec4_t_mem_S h.sylow h.involution
  have hN : S ≤ normalizer (L : Set G) :=
    fun c hc => sec4_mem_normalizer h36 h.toSec3SettingLB c (h.sylow.1 hc)
  have hSyl : IsSylow2Of (S ⊓ L) L :=
    sec4_isSylow2Of_inf h.component.le (sec4_mem_normalizer h36 h.toSec3SettingLB) h.sylow
  exact ⟨hpsp, htC, htnotL, htS, hN, hSyl⟩

end CFSG.OddStandard.SmallF3.Omega
