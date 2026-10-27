module

public import CFSG.Monster.B.GSide.TwoDNative
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBTwoDFixLayers
public import Certificates.Certificate15082

public noncomputable section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.GSide

section Checks


theorem rows_check : rowsCheck = true := Certificates.certificate15082.1

theorem q_check : qCheck = true := Certificates.certificate15082.2.1

theorem alpha_check : alphaCheck = true := Certificates.certificate15082.2.2.1

theorem pauli_check : pauliCheck = true := Certificates.certificate15082.2.2.2.1

theorem comm_check : commCheck = true := Certificates.certificate15082.2.2.2.2.1

theorem u7_check : u7Check = true := Certificates.certificate15082.2.2.2.2.2.1

theorem beta_check : betaCheck = true := Certificates.certificate15082.2.2.2.2.2.2.1

theorem s_check : sCheck = true := Certificates.certificate15082.2.2.2.2.2.2.2

end Checks


theorem sCheck_spec (h : sCheck = true) :
    (∀ x < 256, actWord sWord x < 256 ∧ qN (actWord sWord x ^^^ 64) = qN (x ^^^ 64)) ∧
      rowKey (wWord ++ wWord ++ wWord ++ wWord ++ wWord) = rowKey [] := by
  simp only [sCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  exact h

theorem sD_mem_P4p (hs : sCheck = true) : sD ∈ P4p := wordD_mem_P4p sWord_lt (sCheck_spec hs).1

theorem pow_four_of_mem_Ehat {e : Dfull} (he : e ∈ Ehat) : e ^ 4 = 1 := by
  have h0 : psiD (e * e) = 0 := by rw [psiD_mul he he, ZModModule.add_self]
  have e4 : e ^ 4 = (e * e) * (e * e) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rcases (psiD_eq_zero_iff (Ehat.mul_mem he he)).1 h0 with h | h
  · rw [e4, h, one_mul]
  · rw [e4, h, ← sq, ← orderOf_xhat, pow_orderOf_eq_one]

theorem sD_pow_five (hs : sCheck = true) : sD ^ 5 = 1 := by
  have hw : ∀ k ∈ wWord ++ wWord ++ wWord ++ wWord ++ wWord, k < 44 := by decide
  have hE : wordD (wWord ++ wWord ++ wWord ++ wWord ++ wWord) ∈ Ehat :=
    (projK_eq_one_iff (wordD_mem_Jhat _)).1 (projK_eq_one_of_rowKey hw (sCheck_spec hs).2)
  have e5 : wordD (wWord ++ wWord ++ wWord ++ wWord ++ wWord) = wordD wWord ^ 5 := by
    simp only [wordD_append, pow_succ, pow_zero, one_mul]
  have e4 : sD = wordD wWord ^ 4 := by
    rw [sD, sWord]
    simp only [wordD_append, pow_succ, pow_zero, one_mul]
  rw [e5] at hE
  have h := pow_four_of_mem_Ehat hE
  rw [← pow_mul] at h
  rw [e4, ← pow_mul]
  exact h

@[expose] def sS : Shat := ⟨sD, wordD_mem_Shat sWord⟩

theorem sS_mem_centralizer (hs : sCheck = true) : sS ∈ Subgroup.centralizer ({t2DS} : Set Shat) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (sD_mem_P4p hs).2)

theorem odd_orderOf_sS (hs : sCheck = true) : Odd (orderOf sS) := by
  have h : orderOf sS ∣ 5 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one (sD_pow_five hs)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 h with h | h <;> rw [h] <;> decide

theorem alphaCheck_spec (h : alphaCheck = true) : ∀ m < 512,
    keyOK (rowKey (sWord ++ subWord coGens m)) = true ∧
      keyOK (rowKey (subWord coGens m ++ sWord)) = true ∧
      keyOK (rowKey ([32] ++ subWord coGens m ++ sWord)) = true ∧
      (rowKey (sWord ++ subWord coGens m) = rowKey (subWord coGens m ++ sWord) ∨
        rowKey (sWord ++ subWord coGens m) = rowKey ([32] ++ subWord coGens m ++ sWord) →
        m = 0 ∨ m = 16) := by
  intro m hm
  have h1 := List.all_eq_true.1 h m (List.mem_range.2 hm)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
    beq_iff_eq] at h1
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, h2⟩ := h1
  refine ⟨ha, hb, hc, fun hab => ?_⟩
  rcases h2 with (⟨h3, h4⟩ | h3) | h3
  · exact absurd hab (not_or.2 ⟨h3, h4⟩)
  · exact Or.inl h3
  · exact Or.inr h3

theorem projK_comm {a b : Dfull} (ha : a ∈ Jhat) (hb : b ∈ Jhat) :
    projK (a * b * a⁻¹ * b⁻¹) = projK a * projK b * (projK a)⁻¹ * (projK b)⁻¹ := by
  rw [projK_mul (Jhat.mul_mem (Jhat.mul_mem ha hb) (Jhat.inv_mem ha)) (Jhat.inv_mem hb),
    projK_mul (Jhat.mul_mem ha hb) (Jhat.inv_mem ha), projK_mul ha hb, projK_inv ha, projK_inv hb]

theorem alpha_step (hr : rowsCheck = true) (hq : qCheck = true) (hα : alphaCheck = true)
    (hp : pauliCheck = true) {y : Dfull} (hyL : y ∈ Lgrp) (hc : y * sD * y⁻¹ * sD⁻¹ ∈ T9) :
    y ∈ Ehat ∨ y * ghat8 ∈ Ehat := by
  obtain ⟨m, hm, hmy⟩ := exists_projK_eq hr hq hp hyL
  have hyJ := Amalgam.Lgrp_le_Jhat hyL
  have hsJ : sD ∈ Jhat := wordD_mem_Jhat sWord
  have hlJ := wordD_mem_Jhat (subWord coGens m)
  have hl := subWord_coGens_lt m
  have h1 : ∀ k ∈ sWord ++ subWord coGens m, k < 44 := fun k hk => by
    rcases List.mem_append.1 hk with h | h
    · exact sWord_lt k h
    · exact hl k h
  have h2 : ∀ k ∈ subWord coGens m ++ sWord, k < 44 := fun k hk => by
    rcases List.mem_append.1 hk with h | h
    · exact hl k h
    · exact sWord_lt k h
  have h3 : ∀ k ∈ [32] ++ subWord coGens m ++ sWord, k < 44 := fun k hk => by
    rcases List.mem_append.1 hk with h | h
    · rcases List.mem_append.1 h with h | h
      · rw [List.mem_singleton.1 h]
        norm_num
      · exact hl k h
    · exact sWord_lt k h
  obtain ⟨hk1, hk2, hk3, hfin⟩ := alphaCheck_spec hα m hm
  set A := projK (wordD (subWord coGens m))
  set B := projK sD
  have eSL : projK (wordD (sWord ++ subWord coGens m)) = B * A := by
    rw [wordD_append, projK_mul (wordD_mem_Jhat sWord) hlJ]
    rfl
  have eLS : projK (wordD (subWord coGens m ++ sWord)) = A * B := by
    rw [wordD_append, projK_mul hlJ (wordD_mem_Jhat sWord)]
    rfl
  have eRLS : projK (wordD ([32] ++ subWord coGens m ++ sWord)) = Co2Inv.rK * (A * B) := by
    rw [wordD_append, wordD_append,
      projK_mul (Jhat.mul_mem (wordD_mem_Jhat _) hlJ) (wordD_mem_Jhat sWord),
      projK_mul (wordD_mem_Jhat _) hlJ, show wordD [32] = lftD 32 * 1 from rfl, mul_one,
      projK_lftD_32, mul_assoc]
    rfl
  have hK := projK_comm hyJ hsJ
  rw [hmy] at hK
  have hm0 : m = 0 ∨ m = 16 := by
    apply hfin
    rcases projK_T9 hc with h | h
    · left
      rw [hK] at h
      have hAB : A * B = B * A := by
        calc A * B = A * B * A⁻¹ * B⁻¹ * (B * A) := by group
          _ = B * A := by rw [h, one_mul]
      rw [← rowKey_eq_of_projK_eq h1 h2 (by rw [eSL, eLS, hAB]) hk1 hk2]
    · right
      rw [hK] at h
      have hAB : B * A = Co2Inv.rK * (A * B) := by
        calc B * A = Co2Inv.rK⁻¹ * (A * B * A⁻¹ * B⁻¹ * (B * A)) := by rw [h]; group
          _ = Co2Inv.rK * (A * B) := by rw [rK_inv]; group
      rw [← rowKey_eq_of_projK_eq h1 h3 (by rw [eSL, eRLS, hAB]) hk1 hk3]
  rcases hm0 with rfl | rfl
  · left
    have e : projK y = 1 := by
      rw [hmy]
      show projK (wordD (subWord coGens 0)) = 1
      rw [show subWord coGens 0 = [] by decide, wordD_nil]
      exact projK_one
    exact (projK_eq_one_iff hyJ).1 e
  · right
    have e : projK y = Co2Inv.rK := by
      rw [hmy]
      show projK (wordD (subWord coGens 16)) = Co2Inv.rK
      rw [show subWord coGens 16 = [32] by decide, show wordD [32] = lftD 32 * 1 from rfl,
        mul_one, projK_lftD_32]
    refine (projK_eq_one_iff (Jhat.mul_mem hyJ ghat8_mem_Jhat)).1 ?_
    rw [projK_mul hyJ ghat8_mem_Jhat, e, projK_of_mem ghat8_mem_Jhat, jhatToKv0_ghat8,
      Co2Inv.rK_mul_self]

theorem beta_step (hr : rowsCheck = true) (hq : qCheck = true) (hp : pauliCheck = true)
    (hc : commCheck = true) (hu : u7Check = true) (hβ : betaCheck = true) {e : Dfull}
    (heL : e ∈ Lgrp) (heE : e ∈ Ehat) (hcomm : e * sD * e⁻¹ * sD⁻¹ ∈ T9) : e ∈ T9 := by
  obtain ⟨m, hm, hψ⟩ := exists_psiD_eq hr hq hp heL heE
  rw [psiD_pauliProd] at hψ
  have hsJ : sD ∈ Jhat := wordD_mem_Jhat sWord
  have hcE : e * sD * e⁻¹ * sD⁻¹ ∈ Ehat := by
    rw [show e * sD * e⁻¹ * sD⁻¹ = e * (sD * e⁻¹ * sD⁻¹) by group]
    exact Ehat.mul_mem heE (conj_mem_Ehat' hsJ (Ehat.inv_mem heE))
  obtain ⟨m', hm', u, hu', hcu⟩ := exists_u7Elts_of_mem hcomm hcE
  have h1 : psiD (e * sD * e⁻¹ * sD⁻¹) = vecW (Native.actD 15 commRows m) := by
    rw [psiD_comm heE hsJ, hψ, vecW_add_wAct hp hc]
  have h2 : psiD (e * sD * e⁻¹ * sD⁻¹) = vecW (decodeW (redW u)) := by
    rw [hcu, psiD_u7Elt hp hu hm' hu']
  obtain ⟨hlt, himp⟩ := betaCheck_spec hβ m hm
  have h3 : Native.actD 15 commRows m = decodeW (redW u) :=
    vecW_injective hp hlt (u7Check_spec hu m' hm' u hu').1 (h1.symm.trans h2)
  have h4 : m ∈ u7Idx := himp (h3 ▸ mem_u7Idx.2 ⟨m', hm', u, hu', rfl⟩)
  obtain ⟨m'', hm'', u', hu'', hdec⟩ := mem_u7Idx.1 h4
  have h5 : psiD e = psiD (pcD u') := by rw [hψ, ← hdec, psiD_u7Elt hp hu hm'' hu'']
  have hT := (u7Elts_mem hu'').2.2
  rcases eq_of_psiD_eq heE (pcD_mem_Ehat _) h5 with h | h
  · rw [h]
    exact hT
  · rw [h]
    exact T9.mul_mem (A8_le_T9 xhat_mem_A8) hT

theorem comm_mul_ghat8_mem {y : Dfull} (hyL : y ∈ Lgrp) (hc : y * sD * y⁻¹ * sD⁻¹ ∈ T9) :
    y * ghat8 * sD * (y * ghat8)⁻¹ * sD⁻¹ ∈ T9 := by
  set t := ghat8 * sD * ghat8⁻¹ * sD⁻¹ with ht
  have htA : t ∈ A8 := by
    rw [ht, show ghat8 * sD * ghat8⁻¹ * sD⁻¹ = ghat8 * (sD * ghat8⁻¹ * sD⁻¹) by group]
    exact A8.mul_mem ghat8_mem_A8 (conj_mem_A8 (wordD_mem_NA8 sWord) (A8.inv_mem ghat8_mem_A8))
  have hyt : t * y = y * t := (Subgroup.mem_centralizer_iff.1 hyL) t htA
  have e : y * ghat8 * sD * (y * ghat8)⁻¹ * sD⁻¹ = y * t * y⁻¹ * (y * sD * y⁻¹ * sD⁻¹) := by
    rw [ht]
    group
  have e2 : y * t * y⁻¹ = t := by rw [← hyt, mul_inv_cancel_right]
  rw [e, e2]
  exact T9.mul_mem (A8_le_T9 htA) hc

theorem mem_T9_of_comm (hr : rowsCheck = true) (hq : qCheck = true) (hα : alphaCheck = true)
    (hp : pauliCheck = true) (hc : commCheck = true) (hu : u7Check = true)
    (hβ : betaCheck = true) {y : Dfull} (hyL : y ∈ Lgrp) (hcomm : y * sD * y⁻¹ * sD⁻¹ ∈ T9) :
    y ∈ T9 := by
  rcases alpha_step hr hq hα hp hyL hcomm with hE | hE
  · exact beta_step hr hq hp hc hu hβ hyL hE hcomm
  · have heL : y * ghat8 ∈ Lgrp := Lgrp.mul_mem hyL (A8_le_Lgrp ghat8_mem_A8)
    have h := beta_step hr hq hp hc hu hβ heL hE (comm_mul_ghat8_mem hyL hcomm)
    have e : y = y * ghat8 * ghat8⁻¹ := by group
    rw [e]
    exact T9.mul_mem h (T9.inv_mem (A8_le_T9 ghat8_mem_A8))

theorem fixedPointFree :
    ∀ y ∈ Subgroup.centralizer (T9S : Set Shat),
      (∀ g ∈ Subgroup.centralizer ({t2DS} : Set Shat), Odd (orderOf g) →
        y * g * y⁻¹ * g⁻¹ ∈ T9S) → y ∈ T9S := by
  intro y hy hcomm
  have hyL : (y : Dfull) ∈ Lgrp := by
    rw [Lgrp, Subgroup.mem_centralizer_iff]
    intro a ha
    have h := (Subgroup.mem_centralizer_iff.1 hy) ⟨a, A8_le_Shat ha⟩
      (A8S_le_T9S (mem_A8S.2 ha))
    exact congrArg Subtype.val h
  have h := mem_T9S.1 (hcomm sS (sS_mem_centralizer s_check) (odd_orderOf_sS s_check))
  exact mem_T9S.2 (mem_T9_of_comm rows_check q_check alpha_check pauli_check comm_check u7_check
    beta_check hyL h)

end CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix
