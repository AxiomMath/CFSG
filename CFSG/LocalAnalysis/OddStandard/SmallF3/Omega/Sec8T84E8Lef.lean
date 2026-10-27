module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E8Dat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E4Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E3UpB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E5Fus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E6Gro
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E8Thm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_left_false (F : Sec8T84Base) (h89 : Asc82Lemma89)
    {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G}
    {B E Y1 Y2 : Subgroup G} (hE : Sec8E G t L S z g B E) (hc : Sec8T84XCore G t E Y1 Y2)
    (hleft : S = zpowers t ⊔ (S ⊓ L)) : False := by
  classical
  have hctx : Sec8Ctx G t L S z g B := hE.ctx
  have ht : orderOf t = 2 := hctx.involution
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hsimple : IsSimpleGroup G := hctx.simple
  have hS3 : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS3.component.isQuasisimple, hctx.omega6m⟩
  have hLt : L ≤ centralizer ({t} : Set G) := hS3.component.le
  have hNmem : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer F.h36 hS3
  have hP : IsSylow2Of (S ⊓ L) L := sec4_isSylow2Of_inf hLt hNmem hctx.sylow
  obtain ⟨T, hT, htT, hR⟩ := sec8t84_T_data hE F.hCE F.hAut h89 hLM hP hleft
  obtain ⟨_, hcardT, hTeq, _, _, hT0eq, hcomm, hinf, h12, h21, _,
    hE1T, hE2T, hn1, hn2⟩ := sec8t84_tstruct ht2 hE.elem hc hT htT
  have he1 : CFSG.Open.IsElemAbelian 2 (E ⊓ Y1) := hc.e16_1.1
  have hc1 : Nat.card ↥(E ⊓ Y1) = 16 := by rw [hc.e16_1.2]; norm_num
  have he2 : CFSG.Open.IsElemAbelian 2 (E ⊓ Y2) := hc.e16_2.1
  have hc2 : Nat.card ↥(E ⊓ Y2) = 16 := by rw [hc.e16_2.2]; norm_num
  obtain ⟨B₁, B₂, _, _, _, honly⟩ := F.hM.sylow_E16 G L hLM (S ⊓ L) hP
  have hP' : ∀ B : Subgroup G, B ≤ S ⊓ L → CFSG.Open.IsElemAbelian 2 B →
      Nat.card B = 16 → B = B₁ ∨ B = B₂ := by
    intro B hBle hBe hBcard
    exact honly B hBle ⟨hBe, by rw [hBcard]; norm_num⟩
  have hcomm' : ∀ x ∈ S ⊓ L, x * t = t * x := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLt hx.2)
  have hcardS : Nat.card ↥S = Nat.card ↥(zpowers t ⊔ (S ⊓ L)) :=
    congrArg (fun X : Subgroup G => Nat.card ↥X) hleft
  have hSP : Nat.card ↥S ≤ 2 * Nat.card ↥(S ⊓ L) := by
    rw [hcardS]
    exact sec8t84_card_sup_le ht hcomm'
  have hrank : ∀ A : Subgroup G, A ≤ centralizer ({t} : Set G) →
      CFSG.Open.IsElemAbelian 2 A → Nat.card A < 2 ^ 6 :=
    fun A hA hAe => sec8t84_rank_up (P := S ⊓ L) hctx.sylow inf_le_left hSP hP' hA hAe
  have hfus : ∀ u ∈ T, IsConj t u → ∃ a ∈ T, u = a * t * a⁻¹ :=
    sec8t84_fusion (t := t) (S1 := T ⊓ Y1) (S2 := T ⊓ Y2) (E1 := E ⊓ Y1)
      (E2 := E ⊓ Y2) (T0 := T ⊓ (Y1 ⊔ Y2)) (T := T)
      ht2 hT0eq hTeq hcomm hinf h12 h21 hE1T hE2T he1 hc1 he2 hc2 hn1 hn2 hrank
  have hTsyl : IsSylow2Of T ⊤ := sec8t84_sylow_growth hT.2.1 htT hR hfus
  have hno : ∀ u ∈ (T ⊓ Y1) ⊔ (T ⊓ Y2), ¬ IsConj t u :=
    sec8t84_no_conj_T0 (t := t) (S1 := T ⊓ Y1) (S2 := T ⊓ Y2) (E1 := E ⊓ Y1)
      (E2 := E ⊓ Y2) ht2 hcomm hinf hE1T hE2T he1 hc1 he2 hc2 hn1 hn2 hrank
  have hidx : (T ⊓ (Y1 ⊔ Y2)).relIndex T = 2 := by
    have hmul := Subgroup.relIndex_mul_card (H := T ⊓ (Y1 ⊔ Y2)) (K := T)
    rw [show (T ⊓ (Y1 ⊔ Y2)) ⊓ T = T ⊓ (Y1 ⊔ Y2) from
      inf_eq_left.mpr (inf_le_left : T ⊓ (Y1 ⊔ Y2) ≤ T)] at hmul
    have hrel : (T ⊓ (Y1 ⊔ Y2)).relIndex T * Nat.card ↥(T ⊓ (Y1 ⊔ Y2)) =
        2 * Nat.card ↥(T ⊓ (Y1 ⊔ Y2)) := by
      rw [hmul, hcardT]
    exact Nat.mul_right_cancel Nat.card_pos hrel
  have hcard : 2 < Nat.card G := by
    calc 2 < 2 ^ 8 := by norm_num
      _ = Nat.card ↥E := hE.elem.2.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group E
  have hnc : ∀ x : G, x⁻¹ * t * x ∉ T ⊓ (Y1 ⊔ Y2) := by
    intro x hx
    exact hno (x⁻¹ * t * x) (hT0eq ▸ hx)
      (isConj_iff.mpr ⟨x⁻¹, by rw [inv_inv]⟩)
  exact sec8t84_thompson_false hsimple hcard hTsyl inf_le_left hidx ht2 ht1 htT hnc

end CFSG.OddStandard.SmallF3.Omega
